## Part XIII. Sc⁺-multisections (HWZ Chapter 13, §§13.1–13.5)

Chapter 13 (Springer 2021, pp. 599–636; 2017 numbers in parentheses) builds the perturbations used by the Fredholm theory on ep-groupoids. The perturbations are sc⁺-multisections: functors $\Lambda : W \to \mathbb Q^+$ on a strong bundle $P : W \to X$ that near every point are given by finitely many sc⁺-sections with rational weights. The chapter has five sections. §13.1 constructs *good systems of neighbourhoods*. In such a system every point $x$ has a neighbourhood $U(x)$ that carries the natural action of the isotropy group $G_x$. The target map is proper on the morphisms leaving $\operatorname{cl}U(x)$. And the morphisms from $U(x)$ to $U(x')$ split into components on which source and target are sc-diffeomorphisms onto their images. The section's statements are Lemma 13.1.1, Definition 13.1.2, Proposition 13.1.3, Definitions 13.1.4 and 13.1.5, Lemma 13.1.6, Theorems 13.1.7 and 13.1.8, and Proposition 13.1.9 (2017: Lemma 13.1, Definition 13.1, Proposition 13.1, Definitions 13.2 and 13.3, Lemma 13.2, Theorems 13.1 and 13.2, Proposition 13.2). §13.2 defines the supports, pointwise norms and triviality of sc⁺-multisections. It also defines symmetric section structures, decorated sc⁺-multisections, and the algebra of sums, scalar multiples, products with functions and locally finite sums: Definitions 13.2.1–13.2.5, Lemma 13.2.6, Definitions 13.2.7–13.2.10, Lemma 13.2.11, Definition 13.2.12 and Lemma 13.2.13 (2017: Definitions 13.4–13.8, Lemma 13.3, Definitions 13.9–13.12, Lemma 13.4, Definition 13.13, Lemma 13.5). §13.3 introduces correspondences between index sets. With them it defines structurable and structured sc⁺-multisections, proves that sums, multiples and locally finite sums of structurable ones are structurable, and introduces the tight structures (Definitions 13.3.1–13.3.11, Proposition 13.3.12, Lemma 13.3.14, Proposition 13.3.15, Definition 13.3.17, Corollary 13.3.18, Proposition 13.3.19; 2017: Definitions 13.14–13.21, Propositions 13.3–13.5, Lemma 13.6, Corollary 13.1). §13.4 moves structured sc⁺-multisections along strong bundle equivalences and proper strong bundle coverings, extends them from an open set that meets every orbit, and defines commensurable sums (Theorems 13.4.1, 13.4.3, 13.4.4, Proposition 13.4.2, Definition 13.4.5; 2017: Theorems 13.3–13.5, Proposition 13.6, Definition 13.22). §13.5 defines atomic sc⁺-multisections, the ones built from a single point. It proves that they are structurable and constructs them from bump functions. It also shows that every structured sc⁺-multisection is a locally finite commensurable sum of atomic ones (Definition 13.5.1, Theorems 13.5.3–13.5.7; 2017: Definition 13.23, Theorems 13.6–13.10).

**What is proved, and what is not.** Every numbered statement of Chapter 13 is formalized and proved, and no point of the chapter is open.

*§13.1.*
- Lemma 13.1.1 is proved in a stronger form, without the invariance of $V$ (§XIII.1).
- Definition 13.1.2 is restated: "carries the natural $G_x$-action" is read as an invariant open subset of the domain of a natural representation (§XIII.2).
- Proposition 13.1.3 and Definition 13.1.4 hold as printed in that reading (§XIII.2).
- Definition 13.1.5, the natural bi-action, is written as the formula its proofs use, with its action laws and its sc-smoothness. Lemma 13.1.6 is proved in a stronger form (§XIII.3).
- Theorem 13.1.7 is proved in two forms.
  - A stronger form reads properness in $X$ and needs neither $Q$ open nor any condition on the closures of the new neighbourhoods (§XIII.4).
  - The form as printed reads properness in the full subcategory on the open set $Q$ (§XIII.5).
- Theorem 13.1.8 is proved as printed (§XIII.6).
- Proposition 13.1.9 is proved in a stronger form, with uniqueness among all maps (§XIII.7).

*§13.2.*
- Definition 13.2.1 is Chapter 11's.
- Definitions 13.2.2 and 13.2.4 and the claims after them hold as printed. Definition 13.2.3 is restated as a supremum that is shown to be attained (§XIII.8).
- Definition 13.2.5 is restated on the domain of a natural representation. Lemma 13.2.6 is proved as printed. The symmetric structures on neighbourhoods with the natural action, which the later definitions need, are formalized with it (§XIII.9).
- Definitions 13.2.7 and 13.2.8 hold as printed (§XIII.10).
- Definition 13.2.9 is restated. When the intersection $U'(x) \cap U''(x)$ carries no single natural action for both structures, it is read as a neighbourhood inside it on which the two actions agree. The remark after it, that there are in general no inverses, is proved by an example (§XIII.11).
- Definition 13.2.10 and Lemma 13.2.11 are proved as printed (§XIII.12).
- Definition 13.2.12 is as printed. Lemma 13.2.13 is restated, the infinite sum being written out (§XIII.13).

*§13.3.*
- The correspondences of Definitions 13.3.1–13.3.4, Example 13.3.3 and Remark 13.3.5 are formalized. Definition 13.3.2 also gets the action laws, which the text does not state (§XIII.14).
- Definitions 13.3.6–13.3.11 and Remark 13.3.7 are formalized (§XIII.15).
- Proposition 13.3.12 is restated: "we may assume $\mathcal U_1 = \mathcal U_2$" is carried out (§XIII.16).
- Remark 13.3.13 is proved in its positive half; the negative half has no formal statement. Lemma 13.3.14 is as printed (§XIII.16).
- The construction before Proposition 13.3.15 is proved in a stronger form, with a compatibility the text does not check (§XIII.17).
- Proposition 13.3.15 has bijections in place of equalities of index sets (§XIII.17).
- Definition 13.3.17 and Corollary 13.3.18 are as printed (§XIII.17).
- Proposition 13.3.19 is restated. It holds as printed for a nonempty family, and for every family once a good system exists. The product of correspondences that the text leaves to the reader is written out (§XIII.18).
- Remarks 13.3.9 and 13.3.16 are prose.

*§13.4.*
- Theorem 13.4.1 is proved in a stronger form: the canonical structure is a map of structured classes, independent of all choices (§XIII.19).
- Proposition 13.4.2 is restated. The project has no strong bundle over an open sub-ep-groupoid, so "$\Lambda$ structured on $W|V$" is read as structured data relative to $V$, and "canonical" as uniqueness among the functors on $W$ that extend $\Lambda$ (§XIII.21).
- Theorem 13.4.3 is proved as printed, without Proposition 13.4.2 (§XIII.22).
- Theorem 13.4.4 is proved as printed, with the same canonicity as Theorem 13.4.1 (§XIII.23).
- Definition 13.4.5 is formalized, with the well-definedness the text calls evident proved (§XIII.24).

*§13.5.*
- Definition 13.5.1 is restated on the domain of a natural representation, and read also on neighbourhoods with the natural action, an extra (§XIII.25).
- Theorem 13.5.3 is narrower by one added hypothesis, that a good system exists. It is necessary, since structurability includes a good system, and paracompactness of $|X|$ supplies it (§XIII.26).
- Theorems 13.5.4 and 13.5.6 are narrower only through the pointwise reading of "admits sc-smooth bump functions"; in other respects their conclusions are stronger (§§XIII.27, XIII.29).
- Theorem 13.5.5 is narrower by $I \neq \emptyset$, which the printed formula presupposes. Its last clause carries the same good-system hypothesis as Theorem 13.5.3 (§XIII.28).
- Theorem 13.5.7 is proved in a stronger form: for every structured lift, with partitions of unity and without the paracompactness of $|X|$. It is proved with pieces atomic on neighbourhoods with the natural action, and also with pieces atomic in the sense of Definition 13.5.1, on connected domains (§XIII.30).
- Remark 13.5.2 is prose.

*Points.* The points G.141 (Theorem 13.1.7 as printed), G.142 (decorated sc⁺-multisections and their algebra), G.143 (no inverses), G.148 (Proposition 13.3.19), G.149 (Theorem 13.5.3 and the last clause of Theorem 13.5.5) and G.163 (Proposition 13.4.2) are all closed. No statement of Chapter 13 was found that does not hold as we read it.

**Four decisions that shape the chapter.**
1. *Neighbourhoods with the natural action.* The project's natural representation of $G_x$ (Theorem 7.1.13, Part VII) has a connected domain. The invariant subsets of §13.1 need not be connected. A neighbourhood with the natural action is therefore a natural representation together with an open $U \ni x$ inside its domain, invariant under every $\Phi(g)$ ⟦Chapter13/GoodSystem · EpGroupoid.NatNbhd⟧. In this reading every claim of §13.1 that an invariant open subset carries the natural action holds as printed, and the good systems of §13.1 are made of such neighbourhoods. Definitions 13.2.5 and 13.5.1, which predate the good systems in the formalization, ask for the connected domain of a natural representation, the reading of Chapter 11. The structures on good systems (§§XIII.9–XIII.10) are therefore formalized on neighbourhoods with the natural action. Theorem 13.5.7 is proved both with pieces atomic on such neighbourhoods and with pieces atomic on connected domains, as Definition 13.5.1 asks (§XIII.30).
2. *Components named by a point.* A component of $\mathcal U(x, x')$ is the connected component in $\mathcal U(x, x')$ of one of its morphisms, and it is empty if the morphism is not in $\mathcal U(x, x')$. No statement needs a separate index set of components, and many statements need no membership hypothesis.
3. *Multisections as functors, structures as data.* An sc⁺-multisection is a functor $\Lambda : W \to \mathbb Q^+$ satisfying Chapter 11's predicate, with local section structures on open sets ⟦Chapter11/MultisectionLocalStructure · SBLocalization.IsScPlusMultisection⟧ ⟦Chapter11/MultisectionLocalStructure · SBLocalization.IsLocalRepOn⟧. Decorations, structures and structured tuples are data attached to it. The decorated and structured multisections of the text are quotients of the data by the equivalences of Definitions 13.2.8 and 13.3.8.
4. *Index sets are types.* The text writes equalities of index sets: $I'_x = \{*\}$ and $I'_x = I_x$ in Proposition 13.3.15, $I_x = I'_x$ in Definition 13.3.8, $K_x = \prod_lK^l_x$ in Proposition 13.3.19. The formalization has types with bijections between them, and compares correspondences after relabelling along the bijections. Where the text asks two index sets to be equal (Definitions 13.3.8 and 13.4.5), the formalization asks for an equality of types and compares the correspondences through it.

**Hypotheses added, and their witnesses.** Each added hypothesis is not derived from the text.
- *A good system exists.* Added in Theorem 13.5.3, in the last clause of Theorem 13.5.5, and in Proposition 13.3.19 for the empty family (§§XIII.18, XIII.26, XIII.28). It is necessary. Definition 13.3.6 includes a good system in every structure, so for atomic $\Lambda$ structurability is equivalent to it. Witnesses:
  - Theorem 13.1.8 for paracompact $|X|$.
  - In particular every M-polyfold seen as a trivial ep-groupoid ⟦Chapter13/GoodSystemExistence · EpGroupoid.nonempty_goodSystem_trivial⟧ ⟦Chapter7/EpGroupoid · EpGroupoid.hasParacompactOrbitSpace_trivial⟧, and the bundles $\mathbb R^n \times \mathbb R^k \to \mathbb R^n$ used in Chapter 15 ⟦Chapter15/GeneralPositionAssembly · SBLocalization.nonempty_goodSystem_epSEP_zero⟧.
  - A nonempty family in Proposition 13.3.19 needs nothing, since any member's structure carries a good system.
- *$I \neq \emptyset$ in Theorem 13.5.5* (§XIII.28). An sc⁺-multisection has weights summing to $1$, and with $I = \emptyset$ the printed formula gives $\Lambda = 0$ over $U(x)$. Witness: the families of Construction I, whose index set is $G_x$ (§XIII.27).
- *Pointwise bump functions in Theorems 13.5.4 and 13.5.6* (§§XIII.27, XIII.29). "Admits sc-smooth bump functions" is read as Part XII's pointwise reading of Theorem 12.3.3. Witness: the trivial ep-groupoids $\mathbb R^n$ ⟦Chapter12/BumpEp · EpGroupoid.admitsBumpFunctionsPointwise_trivial_rn⟧.
- *$c \neq 0$ and $k \ge 1$ in the example for the remark that there are no inverses* (§XIII.11). These are parameters of an example, not hypotheses of a statement.
- *Paracompactness of $|X|$ in the existence of decorations and in the structurability of the zero multisection* (§§XIII.10, XIII.15). This is the text's own setting, through Theorem 13.1.8. Witness: as for good systems.

The hypotheses the text states and the formalization keeps without using:
- the properness property in Theorem 13.5.4, and the smoothness of $x$ in its part (2);
- bump functions and the smoothness of $x$ in Theorem 13.5.5;
- the paracompactness of $|X|$ in Theorems 13.5.6 and 13.5.7.

**Map.** All files are in `Polyfold/Chapter13/`. They are grouped by topic.

*Good systems (§13.1).*
- `GoodSystem`: neighbourhoods with the natural action and their invariant cores; Lemma 13.1.1; the sets $\mathcal U(x, x')$ and their components; Definition 13.1.2, Proposition 13.1.3, Definition 13.1.4; families good on a set.
- `BiAction`: the bi-action of Definition 13.1.5 with its laws; the components of a good system; Lemma 13.1.6; stabilizers, $D_\Sigma$, the partner homomorphism, Proposition 13.1.9.
- `GoodSystemExistence`: transports; Theorem 13.1.7 in the stronger form; Theorem 13.1.8; the witness on trivial ep-groupoids.
- `GoodSystemRelative`: the full subcategory on $Q$, properness relative to $Q$, properness by ultrafilters, Theorem 13.1.7 as printed.

*Sc⁺-multisections as functors (§13.2).*
- `ScPlusSectionOn`: sc⁺-sections on open sets, through chart representatives; sums, multiples, finite sums and extensions by $0$.
- `MultisectionSupport`: Definitions 13.2.2–13.2.4 and the claims after them.
- `MultisectionSymmetric`: transported sections, equal weights, Definition 13.2.5, Lemma 13.2.6.
- `MultisectionConvolution`: the convolution of finitely many functors.
- `MultisectionAlgebra`: Definitions 13.2.9 and 13.2.10, Lemma 13.2.11, for functors.
- `MultisectionLocallyFinite`: Definition 13.2.12, Lemma 13.2.13.

*Decorated sc⁺-multisections (§13.2).*
- `SymmetricOn`: the relation "same natural action" between neighbourhoods; moving vectors along morphisms; symmetric structures on a neighbourhood with the natural action and their sums, multiples and products.
- `DecoratedMultisection`: Definitions 13.2.7 and 13.2.8; Definitions 13.2.9, 13.2.10 and Lemmas 13.2.11, 13.2.13 for decorations and on classes.
- `MultisectionNoInverse`: the remark after Definition 13.2.9.

*Correspondences and structurable sc⁺-multisections (§13.3).*
- `Correspondence`: Definitions 13.3.1 and 13.3.2, Example 13.3.3, Remark 13.3.5, products of two correspondences.
- `StructurableMultisection`: Definitions 13.3.4, 13.3.6, 13.3.8, 13.3.10, 13.3.11; Proposition 13.3.12; Lemma 13.3.14; the zero multisection as witness.
- `TightMultisection`: $T_\Lambda$; the construction before Proposition 13.3.15; Proposition 13.3.15, Definition 13.3.17, Corollary 13.3.18.
- `PiCorrespondence`: products of families of correspondences; reindexing symmetric structures.
- `TightOn`: tight versions over a given adapted good system.
- `LocallyFiniteStructurable`: the data of the proof of Proposition 13.3.19, the product structure, Proposition 13.3.19.
- `LocallyFiniteSupports`: from locally finite domain supports to Definition 13.2.12; Proposition 13.3.19 with the printed hypothesis.

*Pull-backs, push-forwards, extension and commensurable sums (§13.4).*
- `StrongBundlePullMap`: the common data of a pull-back; equivalences and proper coverings as such data; pulled-back sections.
- `MultisectionPullback`: adapted neighbourhoods; the pulled-back structure; canonicity; Theorems 13.4.1 and 13.4.4.
- `SymmetricStructurePush`: charts along a morphism; push neighbourhoods; pushed sections and structures.
- `MultisectionPushforward`: lifted morphisms; the pushed good system and structure; Theorem 13.4.3; generalized strong bundle isomorphisms.
- `StructuredExtensionData`: functors and sc⁺-multisections on $W|V$; structured data on $V$; the extension functor; unit charts; extension charts.
- `StructuredExtension`: the extended structure, Proposition 13.4.2.
- `Commensurable`: common data $c$; count transport along correspondences; Definition 13.4.5 and the locally finite commensurable sum.

*Atomic sc⁺-multisections (§13.5).*
- `AtomicMultisection`: Definition 13.5.1; the multisection of atomic data; its local structure.
- `AtomicConstruction`: symmetric families; Theorems 13.5.4, 13.5.5 (existence and uniqueness) and 13.5.6.
- `AtomicStructurableLocal`: the local alternative of the proof of Theorem 13.5.3, and the form of Theorems 13.5.3 and 13.5.5 with structurability as a parameter.
- `AtomicStructurable`: the data and the structure of the proof of Theorem 13.5.3; Theorem 13.5.3; the last clause of Theorem 13.5.5.
- `AtomicSum`: atomic data on a neighbourhood with the natural action; Theorem 13.5.7.
- `Theorem1357Atomic`: the natural representation on a connected component; Theorem 13.5.7 with summands atomic in the sense of Definition 13.5.1.

**Conventions.** Throughout, $X$ is an ep-groupoid with source and target maps $s$, $t$, composition $\circ$, inversion $\varphi \mapsto \varphi^{-1}$ and orbit map $\pi : X \to |X|$. The isotropy group $G_x$ is finite (Proposition 7.1.12, Part VII). A natural representation of $G_x$ (Theorem 7.1.13, Part VII) on an open connected $U \ni x$ consists of sc-diffeomorphisms $\Phi(g) : U \to U$ and morphisms $\Gamma(g, z) : z \to \Phi(g)(z)$. Every morphism between two points of $U$ is $\Gamma(g, z)$ for exactly one $g$. We write $g * z = \Phi(g)(z)$. For $U, U' \subset X$,
$$\mathcal U(U, U') = \{\varphi : s(\varphi) \in U,\ t(\varphi) \in U'\}$$
⟦Chapter13/GoodSystem · EpGroupoid.morBetween⟧, and $\mathcal U(x, x') = \mathcal U(U(x), U(x'))$ for a family of neighbourhoods. A subset $A \subset X$ has *proper closure*, or the properness property, if $t : s^{-1}(\operatorname{cl}A) \to X$ is proper. From §XIII.8 on, $(P : W \to X, \mu)$ is a strong bundle over $X$, $0_x$ the zero of the fibre $W_x$, and $\Lambda : W \to \mathbb Q^+$.

### XIII.1 Neighbourhoods with the natural action, and Lemma 13.1.1 (2017: Lemma 13.1)

**Definition** ⟦Chapter13/GoodSystem · EpGroupoid.NatNbhd⟧. A *neighbourhood of $x$ with the natural action* is a pair $N = (R, U)$:
- $R$ is a natural representation of $G_x$ on the connected open domain $U_R$, with maps $\Phi$, $\Gamma$;
- $U$ is an open subset with $x \in U \subset U_R$ and $\Phi(g)(U) \subset U$ for all $g \in G_x$.

All the laws of $R$ restrict to $U$. On $U$:
- $\Phi(g)$ maps $U$ into $U$;
- $\Gamma(g, z)$ has source $z$ and target $g * z$;
- $\Gamma(1, z)$ is the unit;
- $\Gamma(gh, z) = \Gamma(g, h * z) \circ \Gamma(h, z)$;
- $\Gamma(g^{-1}, g * z) = \Gamma(g, z)^{-1}$;
- $\Gamma(\cdot, z)$ is injective in $g$;
- every morphism between two points of $U$ is $\Gamma(g, \cdot)$ for a unique $g$;
- $\pi(g * z) = \pi(z)$.

*Reading.* The text says "$U(x)$ is $G_x$-invariant and carries the natural action". The project's natural representations live on connected domains. Proposition 13.1.3 shrinks the neighbourhoods of a good system to arbitrary invariant open subsets, which need not be connected, so the neighbourhood is an invariant open subset of such a domain. Since the domain is open and $U$ lies inside it, the uniqueness clause for morphisms between points of $U$ holds as for the domain itself. Nothing in §13.1 uses connectedness of $U(x)$.

**Invariant cores.** For a neighbourhood $N$ with the natural action and an open set $V \ni x$, the *invariant core* is
$$U \cap \bigcap_{g \in G_x}\Phi(g)^{-1}(V)$$
⟦Chapter13/GoodSystem · EpGroupoid.NatNbhd.invariantCore⟧. It is open because $G_x$ is finite and each $\Phi(g)$ is continuous. It contains $x$, because $\Phi(g)(x) = x$. It is invariant, because $\Phi(h)$ maps it into itself by the action law $\Phi(g) \circ \Phi(h) = \Phi(gh)$. And it lies in $U \cap V$, taking $g = 1$. So every neighbourhood with the natural action has, inside any open $V \ni x$, a smaller one with the same natural representation ⟦Chapter13/GoodSystem · EpGroupoid.NatNbhd.exists_restrict_subset⟧. This is the step "we may assume $U(x)$ is invariant" that the text uses throughout.

**Existence with the properness property** ⟦Chapter13/GoodSystem · EpGroupoid.exists_natNbhd_isProperSubset⟧. Inside every open $W \ni x$ there is a neighbourhood $N$ of $x$ with the natural action and with $t : s^{-1}(\operatorname{cl}U) \to X$ proper.
- *Step 1.* Chapter 7 gives, inside any open set around $x$, an open neighbourhood $U_0 \subset W$ of $x$ that is the domain of a natural representation and whose closure has the properness property (the invariant neighbourhoods of Theorem 7.1.13, Part VII).
- *Step 2.* The neighbourhood is that representation with $U = U_0$. It is invariant because it is the domain.

This is the source of all the neighbourhoods in Chapter 13. Every construction below starts from it and shrinks by invariant cores.

**Lemma 13.1.1** (stronger), p. 599 ⟦Chapter13/GoodSystem · EpGroupoid.lemma_13_1_1⟧. Let $N$ be a neighbourhood of $x$ with the natural action, with $t : s^{-1}(\operatorname{cl}U) \to X$ proper, and let $V \subset U$ be any subset. Then
$$\operatorname{cl}_XV \subset U \iff \operatorname{cl}_{|X|}\pi(V) \subset \pi(U).$$
The text assumes $V$ invariant. The form with that assumption follows at once ⟦Chapter13/GoodSystem · EpGroupoid.lemma_13_1_1_book⟧. The two directions use different halves of the hypotheses: (⇒) uses only properness, and (⇐) uses only the natural action.

*Proof of (⇒).* Suppose $\operatorname{cl}V \subset U$. Then $\operatorname{cl}V \subset \operatorname{cl}U$, so $\operatorname{cl}V$ is a closed subset of a set with proper closure.
1. For a closed set $A$ with $t$ proper on $s^{-1}(A)$, the orbit map satisfies $\pi(\operatorname{cl}A) = \operatorname{cl}\pi(A)$ (Proposition 7.1.10, Part VII).
2. Apply this to $\operatorname{cl}V$: $\operatorname{cl}_{|X|}\pi(V) \subset \operatorname{cl}_{|X|}\pi(\operatorname{cl}V) = \pi(\operatorname{cl}V) \subset \pi(U)$.

*Proof of (⇐).* Suppose $\operatorname{cl}\pi(V) \subset \pi(U)$, and let $y \in \operatorname{cl}V$.
1. $\pi(y) \in \operatorname{cl}\pi(V) \subset \pi(U)$, so there is a point $z \in U$ and a morphism $\varphi : z \to y$.
2. The target map is a local sc-diffeomorphism, so near $\varphi$ there is a sheet: a local inverse $\tau$ of $t$ on an open $V' \ni y$ with $\tau(y) = \varphi$, continuous, with $t(\tau(y')) = y'$. Set $O = V' \cap \tau^{-1}(s^{-1}(U))$. It is an open neighbourhood of $y$, since $s(\tau(y)) = z \in U$ and $U$ is open.
3. For $y' \in O \cap V$, $\tau(y')$ is a morphism from $s(\tau(y')) \in U$ to $y' \in V \subset U$. It is therefore $\Gamma(g, s(\tau(y')))$ for a unique $g$, and $y' = g * s(\tau(y'))$.
4. Since $y \in \operatorname{cl}V$, the filter $\mathcal N_V(y)$ of neighbourhoods of $y$ within $V$ is nontrivial, and $O \cap V$ belongs to it. The index $g$ of step 3 takes only finitely many values, since $G_x$ is finite (Proposition 7.1.12, Part VII). So some $g_0$ occurs frequently along $\mathcal N_V(y)$: every neighbourhood of $y$ contains points $y' \in V$ with index $g_0$.
5. Along these points $y' = \Phi(g_0)(s(\tau(y')))$. As $y' \to y$ along the filter, $s(\tau(y')) \to s(\tau(y)) = z$ by continuity, so the right side tends to $\Phi(g_0)(z)$. By uniqueness of limits in the Hausdorff space $X$, $y = \Phi(g_0)(z) \in U$, since $U$ is invariant.

*Where the formal proof departs from the text.* The text takes $V$ invariant and argues with sequences. The formal proof works with filters, and with "occurs frequently" in place of the pigeonhole over a sequence. It never uses that $V$ is invariant: only $V \subset U$ enters, through step 3.

### XIII.2 Definition 13.1.2 (2017: Definition 13.1), Proposition 13.1.3 (2017: Proposition 13.1) and Definition 13.1.4 (2017: Definition 13.2)

**Components and diffeo-components.** For a set $S$ of morphisms and $\varphi \in S$, the component of $\varphi$ is the connected component of $\varphi$ in $S$. For $\varphi \notin S$ it is empty.

A set $\Sigma$ of morphisms is a *diffeo-component* ⟦Chapter13/GoodSystem · EpGroupoid.IsDiffeoComponent⟧ if $s|_\Sigma$ and $t|_\Sigma$ are sc-diffeomorphisms onto open subsets of the objects.

For an open $\Sigma$ this is equivalent to $s$ and $t$ being injective on $\Sigma$ ⟦Chapter13/GoodSystem · EpGroupoid.isDiffeoComponent_iff_injOn⟧, by the following argument.
1. $s$ and $t$ are local sc-diffeomorphisms (Definition 7.1.1 (1), Part VII).
2. An injective local sc-diffeomorphism on an open set is an sc-diffeomorphism onto its image, which is open ⟦Chapter13/GoodSystem · MPolyfold.IsLocalScDiffeo.isScDiffeoOn_invFunOn⟧.
   - The image is open, being a union of the open images of the local sheets.
   - The inverse is the inverse function on the image. Near each image point it agrees with the inverse of one sheet, by injectivity, so it is sc-smooth there.

The components of $\mathcal U(x, x')$ are open, because $\mathcal U(x, x')$ is open ($s$, $t$ continuous, $U(x)$, $U(x')$ open) and the morphism space is locally connected.

**Definition 13.1.2** (restated), p. 600 ⟦Chapter13/GoodSystem · EpGroupoid.GoodSystem⟧. A *good system of neighbourhoods* is a family $(N(x))_{x \in X}$ of neighbourhoods $U(x)$ with the natural action of $G_x$ (condition (2) of the text) such that:
- (1) $t : s^{-1}(\operatorname{cl}U(x)) \to X$ is proper for every $x$;
- (3) for all $x, x'$ and every $\varphi \in \mathcal U(x, x')$, the component of $\varphi$ in $\mathcal U(x, x')$ is a diffeo-component.

By the equivalence above, (3) is the injectivity of $s$ and $t$ on every component. The text's "the images are open" is automatic.

On a good system the inverses $(s|_\Sigma)^{-1}$, $(t|_\Sigma)^{-1}$ are functions on the objects (defined arbitrarily off $s(\Sigma)$, resp. $t(\Sigma)$) ⟦Chapter13/GoodSystem · EpGroupoid.GoodSystem.srcInv⟧. They are sc-smooth on the images. *Restated*: "carries the natural $G_x$-action" is the reading of §XIII.1, and components are named by a point.

**Proposition 13.1.3** (same), p. 600 ⟦Chapter13/GoodSystem · EpGroupoid.proposition_13_1_3⟧. Let $(U(x))$ be a good system and $\tilde U(x) \subset U(x)$ open invariant neighbourhoods of $x$. Then $(\tilde U(x))$ is a good system with the same natural representations ⟦Chapter13/GoodSystem · EpGroupoid.GoodSystem.restrict⟧.

*Proof.*
1. *(2).* $\tilde U(x)$ is open, contains $x$, lies in the domain of the representation of $U(x)$, and is invariant. So it is a neighbourhood with the natural action, with the same representation. This is where decision (1) matters: in the reading "the connected domain of a natural representation", $\tilde U(x)$ could fail to be such a domain, and the proposition would not hold as we read it.
2. *(1).* $\operatorname{cl}\tilde U(x)$ is a closed subset of $\operatorname{cl}U(x)$. A proper map restricted to a closed subset of its domain is proper, so $t : s^{-1}(\operatorname{cl}\tilde U(x)) \to X$ is proper.
3. *(3).* $\tilde{\mathcal U}(x, x') \subset \mathcal U(x, x')$, so the component of $\varphi$ in the smaller set lies in its component in the larger set, on which $s$ and $t$ are injective. Injectivity passes to subsets, and the smaller component is open, so it is a diffeo-component ⟦Chapter13/GoodSystem · EpGroupoid.GoodSystem.isDiffeoComponent_of_subset⟧.

*The step after the proposition.* The text uses the proposition to shrink a good system into given open neighbourhoods $V(x)$. Inside $U(x) \cap V(x)$ the invariant core of §XIII.1 is an invariant open neighbourhood. So every good system has a refinement inside any family of open neighbourhoods ⟦Chapter13/GoodSystem · EpGroupoid.GoodSystem.exists_refinement_subset⟧.

**Definition 13.1.4** (same), p. 600 ⟦Chapter13/GoodSystem · EpGroupoid.GoodSystem.IsRefinement⟧ ⟦Chapter13/GoodSystem · EpGroupoid.GoodSystem.IsSubordinate⟧.
- A good system $\mathcal W$ refines $\mathcal U$ if $W(x) \subset U(x)$ for all $x$.
- $\mathcal U$ is subordinate to an open cover $(O_a)$ if each $U(x)$ lies in some $O_a$.
- The restrictions of Proposition 13.1.3 are refinements ⟦Chapter13/GoodSystem · EpGroupoid.GoodSystem.isRefinement_restrict⟧.

**Families good on a set** ⟦Chapter13/GoodSystem · EpGroupoid.IsGoodOn⟧. Theorems 13.1.7 and 13.1.8 build good systems from partial ones. A family $(N(q))$ of neighbourhoods with the natural action, indexed by all points, is *good on* $Q \subset X$ if for $q, q' \in Q$:
- $U(q) \subset Q$;
- $t : s^{-1}(\operatorname{cl}_XU(q)) \to X$ is proper;
- condition (3) holds on $\mathcal U(q, q')$.

Every good system is good on $X$ ⟦Chapter13/GoodSystem · EpGroupoid.GoodSystem.isGoodOn⟧. A family good on $X$ is a good system. The relation between "good on $Q$" and the text's good system of the sub-ep-groupoid $Q$ is §XIII.5.

### XIII.3 Definition 13.1.5 (2017: Definition 13.3) and Lemma 13.1.6 (2017: Lemma 13.2)

**Definition 13.1.5** (restated), p. 601 ⟦Chapter13/BiAction · EpGroupoid.biact⟧. The text names a map $G_{x'} \times \mathcal U(x, x') \times G_x \to \mathcal U(x, x')$, $(g', \varphi, g) \mapsto g' * \varphi * g$, "the natural bi-action". The formalization writes the formula that the text's proofs use. For neighbourhoods $N = (R, U)$ at $x$ and $N' = (R', U')$ at $x'$, with $\varphi \in \mathcal U(U, U')$:
$$g' * \varphi * g = \Gamma'(g', t(\varphi)) \circ \varphi \circ \Gamma(g, \Phi(g^{-1})(s(\varphi))).$$
- *Source and target.* The source is $\Phi(g^{-1})(s(\varphi))$ ⟦Chapter13/BiAction · EpGroupoid.src_biact⟧ and the target is $\Phi'(g')(t(\varphi))$ ⟦Chapter13/BiAction · EpGroupoid.tgt_biact⟧. The right factor $\Gamma(g, \cdot)$ is taken at $g^{-1} * s(\varphi)$, so that its target is $s(\varphi)$ and the composite is defined.
- *It stays in $\mathcal U$.* By invariance of $U$ and $U'$, $g' * \varphi * g \in \mathcal U(U, U')$ ⟦Chapter13/BiAction · EpGroupoid.biact_mem⟧.
- *Action laws.* $g' * (h' * \varphi * h) * g = (g'h') * \varphi * (hg)$ ⟦Chapter13/BiAction · EpGroupoid.biact_biact⟧. Write out both sides and use associativity of composition with $\Gamma'(g'h', z) = \Gamma'(g', h' * z) \circ \Gamma'(h', z)$ on the left and the corresponding identity for $\Gamma$ on the right. With $1 * \varphi * 1 = \varphi$, from $\Gamma(1, \cdot) = 1$, this is an action of $G_{x'} \times G_x^{\mathrm{op}}$ ⟦Chapter13/BiAction · EpGroupoid.biactMulAction⟧.
- *Cancellations.* $g' * \varphi * g = g' * \psi * g$ implies $\varphi = \psi$, and $g' * \varphi = h' * \varphi$ implies $g' = h'$. The second holds by right cancellation of $\varphi$ and the injectivity of $\Gamma'(\cdot, t\varphi)$.
- *Sc-smoothness* ⟦Chapter13/BiAction · EpGroupoid.isScSmoothOn_biact⟧. Each $\varphi \mapsto g' * \varphi * g$ is sc-smooth on $\mathcal U(U, U')$.
  - The left action $\varphi \mapsto \Gamma'(g', t\varphi) \circ \varphi$ is sc-smooth because $\Gamma'(g', \cdot)$ is, $t$ is, and composition is sc-smooth on the fibred product.
  - The right action is reduced to a left action by inversion: $\varphi * g = (g^{-1} * \varphi^{-1})^{-1}$ in the bi-action for $\mathcal U(U', U)$.
  - Inversion is an sc-diffeomorphism.

The text defines the map before Lemma 13.1.6 and says it permutes components. On a good system the bi-action is $\mathcal U(x, x') \to \mathcal U(x, x')$ ⟦Chapter13/BiAction · EpGroupoid.GoodSystem.biact⟧, and it maps components onto components ⟦Chapter13/BiAction · EpGroupoid.GoodSystem.image_biact_comp⟧.
1. The bi-action by $(g', g)$ is continuous, so it maps the connected component of $\varphi$ into a connected subset of $\mathcal U(x, x')$ containing $g' * \varphi * g$. That subset lies in the component of $g' * \varphi * g$.
2. The bi-action by $(g'^{-1}, g^{-1})$ maps that component back. So the image is the whole component.

Inversion maps components of $\mathcal U(x, x')$ onto components of $\mathcal U(x', x)$ by the same argument ⟦Chapter13/BiAction · EpGroupoid.GoodSystem.image_inv_comp⟧. The components cover $\mathcal U(x, x')$ and are pairwise disjoint or equal ⟦Chapter13/BiAction · EpGroupoid.GoodSystem.components⟧.

**Two tools.**
- *Same source, left factor* ⟦Chapter13/BiAction · EpGroupoid.GoodSystem.exists_biact_left_of_src⟧. Let $\psi_1, \psi_2 \in \mathcal U(x, x')$ have the same source. Then $\chi = \psi_2 \circ \psi_1^{-1}$ is a morphism from $t(\psi_1)$ to $t(\psi_2)$, two points of $U(x')$. So $\chi = \Gamma'(g', t\psi_1)$ for a unique $g'$, and $\psi_2 = g' * \psi_1 * 1$.
- *Same target, right factor* ⟦Chapter13/BiAction · EpGroupoid.GoodSystem.exists_biact_right_of_tgt⟧. Morphisms with the same target differ by a right factor, by the same argument with $\psi_2^{-1} \circ \psi_1$.

**Lemma 13.1.6** (stronger), p. 602. Let $\mathcal U$ be a good system and $\Sigma$ a component of $\mathcal U(x, x')$.

(1) If $\psi \in \Sigma$ and $g' * \psi * 1 \in \Sigma$, then $g' = 1$ ⟦Chapter13/BiAction · EpGroupoid.GoodSystem.eq_one_of_biact_left_mem⟧.
- $g' * \psi * 1$ has source $\Phi(1)(s\psi) = s\psi$.
- $s$ is injective on $\Sigma$ by condition (3), so $g' * \psi * 1 = \psi$.
- Left cancellation gives $\Gamma'(g', t\psi) = 1_{t\psi} = \Gamma'(1, t\psi)$, and injectivity of $\Gamma'$ in the group element gives $g' = 1$.

The text's (1), $g' * \Sigma = \Sigma \Rightarrow g' = 1$, follows by applying this to one $\psi \in \Sigma$ ⟦Chapter13/BiAction · EpGroupoid.GoodSystem.lemma_13_1_6_one⟧. The stronger form needs one morphism, not the whole component, and Proposition 13.1.9 uses it in that form.

(2) The same on the right: $\psi \in \Sigma$ and $1 * \psi * g \in \Sigma$ imply $g = 1$, using injectivity of $t$ ⟦Chapter13/BiAction · EpGroupoid.GoodSystem.eq_one_of_biact_right_mem⟧ ⟦Chapter13/BiAction · EpGroupoid.GoodSystem.lemma_13_1_6_two⟧.

(3) For two components $\Sigma_1$, $\Sigma_2$, the images $s(\Sigma_1)$ and $s(\Sigma_2)$ are equal or disjoint ⟦Chapter13/BiAction · EpGroupoid.GoodSystem.lemma_13_1_6_three_src⟧, and so are $t(\Sigma_1)$ and $t(\Sigma_2)$ ⟦Chapter13/BiAction · EpGroupoid.GoodSystem.lemma_13_1_6_three_tgt⟧.
- Suppose $s(\varphi_1) = s(\varphi_2)$ with $\varphi_i \in \Sigma_i$. By the first tool, $\varphi_2 = g' * \varphi_1 * 1$.
- The bi-action by $(g', 1)$ maps the component of $\varphi_1$ onto the component of $\varphi_2$, so $\Sigma_2 = g' * \Sigma_1$.
- Since $s(g' * \psi * 1) = s(\psi)$, this gives $s(\Sigma_2) = s(\Sigma_1)$.

No membership hypotheses on the components are needed: the component of a morphism outside $\mathcal U(x, x')$ is empty (decision (2)).

*Stronger* refers to (1) and (2), which need one morphism, not the whole component. The text proves (1) through the sc-diffeomorphism $s|_\Sigma$. The formal proof uses only injectivity, which is all that (3) of Definition 13.1.2 gives directly.

### XIII.4 Theorem 13.1.7 (2017: Theorem 13.1), the stronger form: extending a family good on $Q$

The text states Theorem 13.1.7 (p. 602) for an open $Q \subset X$ with $|Q| = |X|$ and a good system of the full sub-ep-groupoid on $Q$. It extends that system to a good system of $X$ that keeps the given neighbourhoods at the points of $Q$ and has the new neighbourhoods inside given open sets. The formalization proves it twice:
- a stronger form, here, for families good on $Q$ in the sense of §XIII.2, with properness read in $X$;
- the printed form, in §XIII.5, by showing that the printed hypothesis implies the stronger form's.

**Transports** ⟦Chapter13/GoodSystemExistence · EpGroupoid.IsTransport⟧. Let $U \subset X$ be open and $V$ another open set. A transport from $U$ into $V$ is a map $\sigma$ from objects to morphisms with:
- $\sigma$ continuous and injective on $U$;
- $t(\sigma(z)) = z$ for $z \in U$;
- $s(\sigma(z)) \in V$ for $z \in U$.

The units $z \mapsto 1_z$ are a transport from $U$ into $U$.

**Condition (3) passes back along transports** ⟦Chapter13/GoodSystemExistence · EpGroupoid.injOn_comp_of_transport⟧. Let $\sigma$ be a transport from $U$ into $V$ and $\sigma'$ one from $U'$ into $V'$, with $s \circ \sigma$ injective on $U$ and $s \circ \sigma'$ injective on $U'$. Suppose $s$ and $t$ are injective on every component of $\mathcal U(V, V')$. Then $s$ and $t$ are injective on every component of $\mathcal U(U, U')$.
1. Define $F(\varphi) = \sigma'(t\varphi)^{-1} \circ \varphi \circ \sigma(s\varphi)$ on $M = \mathcal U(U, U')$. The composite is defined because $t(\sigma(s\varphi)) = s\varphi$ and $t(\sigma'(t\varphi)) = t\varphi$.
2. $F$ has source $s(\sigma(s\varphi)) \in V$ and target $s(\sigma'(t\varphi)) \in V'$, so $F$ maps $M$ into $\mathcal U(V, V')$.
3. $F$ is continuous on $M$: it is built from $\sigma$, $\sigma'$, $s$, $t$, composition and inversion, each continuous, through the composition lemma for continuous maps into composable pairs.
4. So $F$ maps the component $C$ of $\varphi_0$ in $M$, a connected set, into the component of $F(\varphi_0)$ in $\mathcal U(V, V')$, on which $s$ and $t$ are injective.
5. *Injectivity of $s$ on $C$.* Let $\varphi_1, \varphi_2 \in C$ with $s\varphi_1 = s\varphi_2$.
   - $F(\varphi_1)$ and $F(\varphi_2)$ have the same source $s(\sigma(s\varphi_1))$, so by step 4 they are equal.
   - Their targets agree, so $s(\sigma'(t\varphi_1)) = s(\sigma'(t\varphi_2))$, and injectivity of $s \circ \sigma'$ gives $t\varphi_1 = t\varphi_2$.
   - Cancelling the equal factors $\sigma'(t\varphi_i)^{-1}$ and $\sigma(s\varphi_i)$ in $F(\varphi_1) = F(\varphi_2)$ gives $\varphi_1 = \varphi_2$.
6. *Injectivity of $t$.* Symmetric, through $\sigma$.

**A sheet around a morphism** ⟦Chapter13/GoodSystemExistence · EpGroupoid.exists_isOpen_injOn_src_tgt⟧. Every morphism $\psi$ has an open neighbourhood on which $s$ and $t$ are both injective. Each is a local sc-diffeomorphism, so injective near $\psi$; intersect the two neighbourhoods.

**A transport at each point** ⟦Chapter13/GoodSystemExistence · EpGroupoid.exists_transport_of_isGoodOn⟧. Let the family $(N(q))$ be good on $Q$, with $\pi(Q) = |X|$, and let $W \ni x$ be open. Then there are:
- a point $q \in Q$;
- a neighbourhood $M$ of $x$ with the natural action and proper closure, $M \subset W$;
- a transport from $M$ into $U(q)$ with $s \circ \sigma$ injective on $M$.

*Case $x \in Q$.* Take $q = x$, $M = N(x)$ (inside $W$ by restricting to an invariant core, §XIII.1) and the unit transport.

*Case $x \notin Q$.*
1. Since $\pi(Q) = |X|$ there is $q \in Q$ and a morphism $\psi : q \to x$.
2. Take an open $O_0 \ni \psi$ on which $s$ and $t$ are injective, and set $O = O_0 \cap s^{-1}(U(q))$.
3. $t|_O$ is an injective local sc-diffeomorphism on the open set $O$, so it is an sc-diffeomorphism onto the open set $t(O) \ni x$ (§XIII.2). Its inverse on $t(O)$ is $\sigma = (t|_O)^{-1}$.
4. Choose $M$ with the natural action and proper closure inside $W \cap t(O)$ (§XIII.1).
5. Then $\sigma$ is continuous and injective on $M$, $t(\sigma(z)) = z$, and $s(\sigma(z)) \in U(q)$ since $\sigma(z) \in O$. And $s \circ \sigma$ is injective because $s$ is injective on $O$ and $\sigma$ is injective.

**Theorem 13.1.7, stronger form** (stronger), p. 602 ⟦Chapter13/GoodSystemExistence · EpGroupoid.theorem_13_1_7⟧. Let $Q \subset X$ with $\pi(Q) = |X|$, let $(N(q))$ be good on $Q$ (§XIII.2), and for $y \notin Q$ let $W(y) \ni y$ be open. Then there is a good system $\mathcal U$ of $X$ with:
- $N_{\mathcal U}(q) = N(q)$ for $q \in Q$;
- $U(y) \subset W(y)$ for $y \notin Q$.

*Proof.*
1. *Choices.* For every $y$, choose the data of the previous lemma with $W = W(y)$ for $y \notin Q$ (and $W = X$ for $y \in Q$):
   - a point $q_y \in Q$;
   - a neighbourhood $M(y)$;
   - a transport $\sigma_y$ from $M(y)$ into $U(q_y)$.

   For $y \in Q$ the lemma's first case keeps $M(y) = N(y)$.
2. *The family is good on $X$.*
   - Each $M(y)$ has the natural action and proper closure.
   - Condition (3) for $\mathcal U(y, y')$ follows from condition (3) for $\mathcal U(q_y, q_{y'})$, which holds since the family is good on $Q$. The step is the transport lemma with $\sigma = \sigma_y$, $\sigma' = \sigma_{y'}$.
3. *A family good on all of $X$ is a good system* ⟦Chapter13/GoodSystem · EpGroupoid.GoodSystem.ofIsGoodOn⟧.

*Where the formal proof departs from the text, and why stronger.* The text's hypothesis is a good system of the full sub-ep-groupoid $Q$, with properness read in $Q$, and $Q$ open. Here properness is read in $X$ and $Q$ is any set meeting every orbit. The text also asks the new $U(y)$ to have closures with a further smallness condition; it is not used, and the conclusion holds without it. The printed form is derived from this one in §XIII.5.

### XIII.5 Theorem 13.1.7 (2017: Theorem 13.1) as printed: properness in the full subcategory on $Q$

**The full subcategory on $Q$.** For $Q \subset X$, the morphisms of the full subcategory are the morphisms with source and target in $Q$. Its source and target maps are the restrictions ⟦Chapter13/GoodSystemRelative · EpGroupoid.subSrc⟧ ⟦Chapter13/GoodSystemRelative · EpGroupoid.subTgt⟧, valued in $Q$ with the subspace topology.
- A subset $A \subset Q$ is *proper in $Q$* if $t : s^{-1}(A) \to Q$ is proper in the subcategory ⟦Chapter13/GoodSystemRelative · EpGroupoid.IsProperSubsetIn⟧.
- A family $(N(q))_{q \in Q}$ is a *good system for $Q$* ⟦Chapter13/GoodSystemRelative · EpGroupoid.IsGoodIn⟧ if for $q, q' \in Q$:
  - $U(q) \subset Q$;
  - $\operatorname{cl}_QU(q)$ is proper in $Q$ (Definition 13.1.2 (1) read in $Q$);
  - condition (3) holds on $\mathcal U(q, q')$.

Conditions (2) and (3) are the same in $Q$ and in $X$:
- a natural representation of $G_q$ whose domain lies in $Q$ is one for the ep-groupoid $Q$;
- $\mathcal U(q, q')$ is the same set of morphisms in both, since the subcategory is full.

No sub-ep-groupoid structure is built. The subcategory is its set of morphisms with the restricted maps, which is all the printed hypothesis refers to.

Every good system of $X$ is a good system for $Q = X$ ⟦Chapter13/GoodSystemRelative · EpGroupoid.GoodSystem.isGoodIn_univ⟧. With Theorem 13.1.8 this is the witness of the notion.

**Properness by ultrafilters** (extra) ⟦Chapter13/GoodSystemRelative · EpGroupoid.isProperMap_iff_ultrafilter_of_isInducing⟧. Let $f$ be a continuous map defined on a subspace $S$ of a space $T$. Then $f$ is proper iff the following holds. For every ultrafilter $\mathcal F$ on $T$ that contains $S$ and whose image under $f$ converges to some $b$, $\mathcal F$ converges to some $a \in S$ with $f(a) = b$. This is Mathlib's characterization of proper maps by ultrafilters, transported along the inclusion of the subspace. It turns the two properness notions into statements about ultrafilters of morphisms:
- in $X$ ⟦Chapter13/GoodSystemRelative · EpGroupoid.isProperSubset_iff_ultrafilter⟧;
- in $Q$ ⟦Chapter13/GoodSystemRelative · EpGroupoid.isProperSubsetIn_iff_ultrafilter⟧.

**Two tools.**
- ⟦Chapter13/GoodSystemRelative · EpGroupoid.exists_mor_tgt_mem⟧: if $\pi(Q) = |X|$, every object $z$ has a morphism $z \to q''$ with $q'' \in Q$. It is the inverse of a morphism from a point of $Q$ to $z$.
- ⟦Chapter13/GoodSystemRelative · EpGroupoid.exists_localSection⟧: through a morphism $\chi$ with target in an open $O$ there is a local section $\sigma$ of $s$ near $s(\chi)$, continuous, with:
  - $\sigma(s\chi) = \chi$;
  - $s(\sigma(z)) = z$;
  - $t(\sigma(z)) \in O$.

  It is the local inverse of the local homeomorphism $s$ at $\chi$, cut down by the continuity of $t$ to the preimage of $O$.

**Step 1: the closure stays in $Q$** ⟦Chapter13/GoodSystemRelative · EpGroupoid.closure_subset_of_isProperSubsetIn⟧. Let $Q$ be open with $\pi(Q) = |X|$, $U \subset Q$, and $\operatorname{cl}_QU$ proper in $Q$. Then $\operatorname{cl}_XU \subset Q$.
1. Let $z \in \operatorname{cl}_XU$. Choose $\chi : z \to q''$ with $q'' \in Q$, and a local section $\sigma$ of $s$ through $\chi$, defined on an open $V \ni z$, with targets in $Q$.
2. Let $\mathcal F$ be an ultrafilter finer than the filter of neighbourhoods of $z$ within $U \cap V$. It is nontrivial because $z \in \operatorname{cl}U$ and $V$ is a neighbourhood of $z$.
3. Push $\mathcal F$ forward by $\sigma$. For $y' \in U \cap V$, $\sigma(y')$ is a morphism with source $y' \in U \subset Q$ and target in $Q$, a morphism of the subcategory with source in $\operatorname{cl}_QU$. Its targets $t(\sigma(y'))$ converge to $t(\chi) = q'' \in Q$, by continuity.
4. By properness in $Q$, read through ultrafilters, the pushed ultrafilter converges in the subcategory to a morphism $\rho$ with $t(\rho) = q''$.
5. The pushed ultrafilter also converges in $X$ to $\sigma(z) = \chi$, by continuity of $\sigma$. Limits in the Hausdorff space of morphisms are unique, so $\rho = \chi$.
6. Since $\rho$ is a morphism of the subcategory, its source $z$ lies in $Q$.

**Step 2: properness in $X$** ⟦Chapter13/GoodSystemRelative · EpGroupoid.isProperSubset_of_isProperSubsetIn⟧. Under the same hypotheses, $t : s^{-1}(\operatorname{cl}_XU) \to X$ is proper.
1. By Step 1, $\operatorname{cl}_XU = \operatorname{cl}_QU$.
2. Let $\mathcal F$ be an ultrafilter of morphisms with sources in $\operatorname{cl}_XU$ whose targets converge to $y \in X$.
3. Choose $\chi : y \to q''$ with $q'' \in Q$, and a local section $\rho$ of $s$ through $\chi$ with targets in $Q$.
4. $F(\varphi) = \rho(t\varphi) \circ \varphi$ is defined eventually along $\mathcal F$. It is a morphism of the subcategory with source $s\varphi \in \operatorname{cl}_QU$ and target $t(\rho(t\varphi)) \in Q$, and these targets converge to $t(\chi) = q''$.
5. By properness in $Q$ the image ultrafilter converges to some morphism $\psi$.
6. Then $\varphi = \rho(t\varphi)^{-1} \circ F(\varphi)$ converges to $\chi^{-1} \circ \psi$, by continuity of inversion and composition. This is a limit of $\mathcal F$ with target $y$.

*The converse* ⟦Chapter13/GoodSystemRelative · EpGroupoid.isProperSubsetIn_of_isProperSubset⟧. Properness in $X$ together with $\operatorname{cl}_XU \subset Q$ gives properness in $Q$. An ultrafilter in the subcategory whose targets converge in $Q$ has, by properness in $X$, a limit, whose source lies in $\operatorname{cl}_XU \subset Q$ and whose target is the limit in $Q$, so it is a morphism of the subcategory.

*Consequence* ⟦Chapter13/GoodSystemRelative · EpGroupoid.isGoodIn_iff⟧. For open $Q$ with $\pi(Q) = |X|$, a family is a good system for $Q$ iff it is good on $Q$ in the sense of §XIII.2 and $\operatorname{cl}_XU(q) \subset Q$ for all $q \in Q$.

**Theorem 13.1.7, as printed** (stronger), p. 602 ⟦Chapter13/GoodSystemRelative · EpGroupoid.theorem_13_1_7_book⟧. Let $Q$ be open with $|Q| = |X|$ and $(N(q))_{q \in Q}$ a good system for the ep-groupoid $Q$. Given open $W(y) \ni y$ for $y \notin Q$, there is a good system of $X$ that keeps $N(q)$ for $q \in Q$ and has $U(y) \subset W(y)$ for $y \notin Q$.

*Proof.*
1. A good system for $Q$ is good on $Q$ ⟦Chapter13/GoodSystemRelative · EpGroupoid.IsGoodIn.isGoodOn⟧, by Step 2.
2. The stronger form of §XIII.4 applies ⟦Chapter13/GoodSystemExistence · EpGroupoid.theorem_13_1_7⟧.

No hypothesis is added. The text writes $|Q| = |Y|$ for $\pi(Q) = |X|$. The verdict is "stronger" because the conclusion omits nothing and the smallness condition on the new closures is not required. That condition is a property of the text's construction, not used afterwards in the chapter.

### XIII.6 Theorem 13.1.8 (2017: Theorem 13.2): good systems exist on paracompact orbit spaces

**Finitely many morphisms into a point, and one sheet for a connected set** ⟦Chapter13/GoodSystemExistence · EpGroupoid.exists_nhds_injOn_of_isProperSubset⟧. Let $A_1, \dots, A_n$ be closed sets with proper closure (the properness property), $A = \bigcup_iA_i$, and $y \in X$. Then there is an open $V \ni y$ such that, for every preconnected set $C$ of morphisms from $A$ to $V$, $s$ and $t$ are injective on $C$.
1. *$\Theta$ is finite.* Let $\Theta = \{\varphi : s\varphi \in A,\ t\varphi = y\}$. For each $i$, the morphisms with source in $A_i$ and target $y$ form a fibre of the proper map $t$ on $s^{-1}(A_i)$. The map $t$ is locally injective, so this fibre is discrete and compact, hence finite. A finite union of finite sets is finite.
2. *Separating sheets.* For each $\theta \in \Theta$ choose an open sheet $O'(\theta) \ni \theta$ on which $s$ and $t$ are injective (§XIII.4). Shrink them to be pairwise disjoint, by Hausdorff separation of the finitely many points of $\Theta$. Let $\Omega = \bigcup_\theta O'(\theta)$, an open set.
3. *Closed images.* $B_i = t(s^{-1}(A_i) \setminus \Omega)$ is closed, since $s^{-1}(A_i) \setminus \Omega$ is closed in $s^{-1}(A_i)$ and the proper map $t$ is closed. Also $y \notin B_i$, since every morphism from $A_i$ to $y$ is in $\Theta \subset \Omega$.
4. *The neighbourhood.* $V = \bigcap_i B_i^c$ intersected with $\bigcap_\theta t(O'(\theta))$ is open and contains $y$.
5. *A connected set lies in one sheet.* Let $C$ be preconnected with sources in $A$ and targets in $V$. Every $\varphi \in C$ lies in $\Omega$, since otherwise $t\varphi \in B_i$ for some $i$. The $O'(\theta)$ are disjoint and open, so the preconnected $C$ lies in one of them, on which $s$ and $t$ are injective.

**Theorem 13.1.8** (same), p. 604 ⟦Chapter13/GoodSystemExistence · EpGroupoid.theorem_13_1_8⟧. If $|X|$ is paracompact, then for every family of open $W(x) \ni x$ there is a good system with $U(x) \subset W(x)$ for all $x$.

*Reading.* The text's "for all $\in X$" is read as "for all $x \in X$".

*Proof*, following the text's steps.
1. *Neighbourhoods with proper closure.* For each $x$ choose a neighbourhood $N_0(x)$ with the natural action and proper closure inside $W(x)$ (§XIII.1).
2. *A locally finite shrinking in $|X|$.* The sets $\pi(U_0(x))$ are open in $|X|$, because $\pi$ is open (Proposition 7.1.8, Part VII), and cover $|X|$.
   - Paracompactness gives a locally finite open refinement $(\tilde v_a)_a$ with $\tilde v_a \subset \pi(U_0(a))$.
   - The shrinking lemma for point-finite covers of a normal space gives open $\tilde v'_a$ with $\operatorname{cl}\tilde v'_a \subset \tilde v_a$, still covering. The paracompact Hausdorff space $|X|$ is normal (Part VII).
   - The closures $\operatorname{cl}\tilde v'_a$ are locally finite.
3. *The set $V$.* Let $V_a = \pi^{-1}(\tilde v'_a) \cap U_0(a)$ and $V = \bigcup_aV_a$.
   - $V$ is open and $\pi(V) = |X|$.
   - By Lemma 13.1.1 (⇐), $\operatorname{cl}V_a \subset U_0(a)$, since $\operatorname{cl}\pi(V_a) \subset \operatorname{cl}\tilde v'_a \subset \pi(U_0(a))$. So each $\operatorname{cl}V_a$ has the properness property.
   - The $V_a$ are locally finite, and $\operatorname{cl}V = \bigcup_a\operatorname{cl}V_a$.
4. *Finitely many pieces near each point.* For each $x$ there are an open $G \ni x$ and a finite set $F$ of indices such that every morphism $\varphi$ with $s\varphi \in \operatorname{cl}V$ and $t\varphi \in G$ has $s\varphi \in \operatorname{cl}V_a$ for some $a \in F$.
   - Take $G = \pi^{-1}(\tilde N)$, with $\tilde N$ a neighbourhood of $\pi(x)$ meeting only finitely many $\operatorname{cl}\tilde v'_a$.
   - $\pi(s\varphi) = \pi(t\varphi) \in \tilde N$, and $s\varphi \in \operatorname{cl}V_a$ for some $a$; that $\operatorname{cl}\tilde v'_a$ meets $\tilde N$, so $a \in F$.
5. *The neighbourhoods at points of $V$.* For $x \in V$:
   - take $G$ and $F$ from step 4, and $V'$ from the sheet lemma for $A_a = \operatorname{cl}V_a$, $a \in F$, and $y = x$;
   - let $N_1(x)$ be the invariant core of $N_0(x)$ in $V \cap G \cap V'$.

   Then $N_1(x) \subset W(x)$, it has proper closure (a closed subset of $\operatorname{cl}U_0(x)$), and $U_1(x) \subset V$. For a preconnected set $C$ of morphisms from $\operatorname{cl}V$ to $U_1(x)$, steps 4 and the sheet lemma give $s$, $t$ injective on $C$. For $x \notin V$ keep $N_1(x) = N_0(x)$.
6. *Good on $V$.* For $q, q' \in V$ and a component $\Sigma$ of $\mathcal U(q, q')$:
   - the sources of $\Sigma$ lie in $U_1(q) \subset V \subset \operatorname{cl}V$ and its targets in $U_1(q')$;
   - $\Sigma$ is connected, so by step 5 at $q'$ the maps $s$ and $t$ are injective on it;
   - $\Sigma$ is open, so it is a diffeo-component.

   The other two conditions of "good on $V$" are in step 5.
7. *Extension.* The stronger Theorem 13.1.7 (§XIII.4), with $Q = V$, gives a good system that keeps $N_1(q)$ on $V$ and has $U(y) \subset W(y)$ off $V$.

*Where the formal proof departs from the text.* The steps are the text's. The separation of the finitely many morphisms in the sheet lemma uses only Hausdorff separation and the properness of $t$, and metrizability of $|X|$ is not used anywhere. The neighbourhoods off $V$ come from the stronger Theorem 13.1.7, so the smallness of their closures that the printed Theorem 13.1.7 arranges is not needed.

**The witness** ⟦Chapter13/GoodSystemExistence · EpGroupoid.nonempty_goodSystem_trivial⟧. For every paracompact Hausdorff M-polyfold $Z$, the trivial ep-groupoid on $Z$ (only units) has paracompact orbit space $|X| = Z$ ⟦Chapter7/EpGroupoid · EpGroupoid.hasParacompactOrbitSpace_trivial⟧. Theorem 13.1.8 gives it a good system. So Definition 13.1.2 is not vacuous.

### XIII.7 Proposition 13.1.9 (2017: Proposition 13.2)

**Stabilizers and $D_\Sigma$.** Let $\mathcal U$ be a good system and $\Sigma$ a component of $\mathcal U(x, x')$.
- $G_{x,\Sigma}$ is the set of $g \in G_x$ with $g * s(\Sigma) = s(\Sigma)$ ⟦Chapter13/BiAction · EpGroupoid.GoodSystem.stabSrc⟧.
- $G_{x',\Sigma}$ is the set of $g' \in G_{x'}$ with $g' * t(\Sigma) = t(\Sigma)$ ⟦Chapter13/BiAction · EpGroupoid.GoodSystem.stabTgt⟧.

Both are subgroups. The map
$$D_\Sigma = t \circ (s|_\Sigma)^{-1} : s(\Sigma) \to t(\Sigma)$$
⟦Chapter13/BiAction · EpGroupoid.GoodSystem.D⟧ is an sc-diffeomorphism with inverse $s \circ (t|_\Sigma)^{-1}$ ⟦Chapter13/BiAction · EpGroupoid.GoodSystem.isScDiffeoOn_D⟧. It is a composite of the sc-diffeomorphisms $(s|_\Sigma)^{-1}$ and $t|_\Sigma$ of §XIII.2.

**Proposition 13.1.9** (stronger), p. 607 ⟦Chapter13/BiAction · EpGroupoid.GoodSystem.proposition_13_1_9⟧. There is a group isomorphism $G_{x,\Sigma} \to G_{x',\Sigma}$, $g \mapsto g'(g)$, with
$$(s|_\Sigma)^{-1}(g * z) = g'(g) * (s|_\Sigma)^{-1}(z) * g^{-1} \quad\text{for } z \in s(\Sigma),$$
and every map $G_{x,\Sigma} \to G_{x',\Sigma}$ with this property equals it.

*Proof.*
1. *The partner exists.* Let $g \in G_{x,\Sigma}$ and $\varphi \in \Sigma$. The morphism $1 * \varphi * g^{-1}$ has source $g * s(\varphi)$, which lies in $s(\Sigma)$ since $g$ stabilizes $s(\Sigma)$. So there is $\psi \in \Sigma$ with the same source, and by the first tool of §XIII.3, $\psi = g' * (1 * \varphi * g^{-1}) * 1 = g' * \varphi * g^{-1}$ for some $g'$. Thus there is $g'$ with $g' * \varphi * g^{-1} \in \Sigma$.
2. *It is unique* ⟦Chapter13/BiAction · EpGroupoid.GoodSystem.partner⟧.
   - *Left uniqueness.* If $g'_1 * \varphi * g^{-1}$ and $g'_2 * \varphi * g^{-1}$ both lie in $\Sigma$, they have the same source, so they are equal by injectivity of $s$ on $\Sigma$. Left cancellation in the bi-action gives $g'_1 = g'_2$.
   - *Right uniqueness.* If $g' * \varphi * g_1$ and $g' * \varphi * g_2$ both lie in $\Sigma$, injectivity of $t$ on $\Sigma$ and right cancellation give $g_1 = g_2$.
3. *It does not depend on $\varphi$.* The bi-action by $(g', g^{-1})$ maps the component of $\varphi$, which is $\Sigma$, onto the component of $g' * \varphi * g^{-1}$, which is $\Sigma$ again. So $g' * \psi * g^{-1} \in \Sigma$ for every $\psi \in \Sigma$, with the same $g'$.
4. *It lies in $G_{x',\Sigma}$.* $t(g' * \psi * g^{-1}) = g' * t(\psi)$, so $g' * t(\Sigma) \subset t(\Sigma)$, with equality by the same argument for the inverse. And it satisfies the identity: for $z = s(\psi)$, $(s|_\Sigma)^{-1}(g * z) = g' * \psi * g^{-1}$, since the right side lies in $\Sigma$ and has source $g * z$.
5. *A homomorphism* ⟦Chapter13/BiAction · EpGroupoid.GoodSystem.partnerHom⟧. For $g, h$: $(g'(g)g'(h)) * \varphi * (gh)^{-1} = g'(g) * (g'(h) * \varphi * h^{-1}) * g^{-1}$ by the action law, and it lies in $\Sigma$. Left uniqueness gives $g'(gh) = g'(g)g'(h)$.
6. *Bijective.*
   - Injective: if $g'(g_1) = g'(g_2)$ then $g'(g_1) * \varphi * g_1^{-1}$ and $g'(g_1) * \varphi * g_2^{-1}$ lie in $\Sigma$, and right uniqueness gives $g_1 = g_2$.
   - Surjective: for $k \in G_{x',\Sigma}$, the second tool of §XIII.3 applied to $k * \varphi * 1$ and an element of $\Sigma$ with the same target gives $h$ with $k * \varphi * h \in \Sigma$. One checks $h^{-1} \in G_{x,\Sigma}$, and its partner is $k$.
7. *Uniqueness among all maps.* If $f : G_{x,\Sigma} \to G_{x',\Sigma}$ satisfies the identity, then at $z = s(\varphi)$ the identity says $f(g) * \varphi * g^{-1} = (s|_\Sigma)^{-1}(g * z) \in \Sigma$. Left uniqueness gives $f(g) = g'(g)$.

*Equivariance of $D_\Sigma$* ⟦Chapter13/BiAction · EpGroupoid.GoodSystem.proposition_13_1_9_D⟧: $\Phi'(g'(g)) \circ D_\Sigma = D_\Sigma \circ \Phi(g)$ on $s(\Sigma)$. Apply $t$ to the identity of the proposition: $t(g' * \psi * g^{-1}) = g' * t(\psi)$.

*Where the formal proof departs from the text, and why stronger.* The text proves the identity through the smoothness of a map $\Theta_g$ and a connectedness argument on it, and states uniqueness for homomorphisms. The formal proof uses only Lemma 13.1.6 in its one-morphism form, with the action laws and the cancellations. The uniqueness it proves is among all maps, not only homomorphisms.

### XIII.8 Definition 13.2.1 recalled, sc⁺-sections on open sets, and Definitions 13.2.2–13.2.4 (2017: Definitions 13.4–13.7): supports, norms, triviality

**Definition 13.2.1** (p. 607). $\Lambda : W \to \mathbb Q^+$ is an sc⁺-multisection in Chapter 11's sense ⟦Chapter11/MultisectionLocalStructure · SBLocalization.IsScPlusMultisection⟧ (Definition 13.2.1, Part XI) if two conditions hold.
- $\Lambda$ is a functor: $\Lambda(\mu(\varphi, w)) = \Lambda(w)$ whenever $P(w) = s(\varphi)$.
- Every point $x$ has a *local section structure*: an open $O \ni x$, finitely many sc⁺-sections $s_1, \dots, s_k$ on $O$, and weights $\sigma_1, \dots, \sigma_k \in \mathbb Q^+$, $\sigma_i > 0$, with $\sum_i\sigma_i = 1$ and
$$\Lambda(w) = \sum_{i : s_i(P(w)) = w}\sigma_i \quad\text{for } P(w) \in O$$
⟦Chapter11/MultisectionLocalStructure · SBLocalization.IsLocalRepOn⟧.

This is the definition the whole chapter builds on. The structures of §§13.2–13.5 are additional data on such a functor.

**Sc⁺-sections on an open set.** An sc⁺-section on an open $U$ is a section of $P$ over $U$ with values in $W_{0,1}$ that is sc-smooth as a map into $W_{0,1}$ (Chapter 11). Chapter 13 needs sums, multiples and cut-offs of such sections. The formalization proves the following.
- *Characterization by charts.* Being sc⁺ on $U$ can be tested on chart representatives near each point: the representative of the section in a strong bundle chart, read on the $(0,1)$-level ⟦Chapter13/ScPlusSectionOn · SBLocalization.isScPlusSectionOn_of_localRepOne⟧.
- *Values in $W_{0,1}$.* The values of an sc⁺-section lie in $W_{0,1}$ ⟦Chapter13/ScPlusSectionOn · SBLocalization.IsScPlusSectionOn.mem_oneSet⟧.
- *Sums and multiples.* $s_1 + s_2$ is sc⁺ on $U$ ⟦Chapter13/ScPlusSectionOn · SBLocalization.IsScPlusSectionOn.sectionAdd⟧. So is $\beta s$ for an sc-smooth $\beta : U \to \mathbb R$ ⟦Chapter13/ScPlusSectionOn · SBLocalization.IsScPlusSectionOn.sectionSmul⟧, and in particular $as$ for a constant $a$ ⟦Chapter13/ScPlusSectionOn · SBLocalization.IsScPlusSectionOn.sectionSmul_const⟧. Finite sums are sc⁺ ⟦Chapter13/ScPlusSectionOn · SBLocalization.isScPlusSectionOn_sectionSum⟧, and the zero section is sc⁺ ⟦Chapter13/ScPlusSectionOn · SBLocalization.isScPlusSectionOn_fiberZero⟧. In charts the fibres are linear and the operations are sc-smooth maps of the fibre coordinates, sc⁺ preserved.
- *Extension by zero.* A section defined on $U$ is extended by $0$ off $U$ ⟦Chapter13/ScPlusSectionOn · SBLocalization.extendZero⟧, agrees with the original on $U$ ⟦Chapter13/ScPlusSectionOn · SBLocalization.extendZero_eqOn⟧, and is again sc⁺ on $U$ ⟦Chapter13/ScPlusSectionOn · SBLocalization.IsScPlusSectionOn.extendZero⟧. A local section structure can be replaced by the extended sections ⟦Chapter13/ScPlusSectionOn · SBLocalization.IsLocalRepOn.extendZero⟧. This makes all local sections functions on all objects, which the transports of Lemma 13.2.6 need.

**Definition 13.2.2** (same), p. 608 ⟦Chapter13/MultisectionSupport · SBLocalization.domSupp⟧ ⟦Chapter13/MultisectionSupport · SBLocalization.supp⟧ ⟦Chapter13/MultisectionSupport · SBLocalization.suppAt⟧.
- The *domain support* is $\operatorname{dom-supp}(\Lambda) = \operatorname{cl}\{x : \exists w \in W_x,\ w \neq 0_x,\ \Lambda(w) > 0\}$.
- The *support* is $\operatorname{supp}(\Lambda) = \{w : \Lambda(w) > 0\}$, with fibres $\operatorname{supp}(\Lambda)(x)$.

The text then claims several facts. Each is proved. Let $\Lambda$ be an sc⁺-multisection and $(s_i, \sigma_i)$ a local section structure on $O$.
1. *On $O$ the support is the set of section values* ⟦Chapter13/MultisectionSupport · SBLocalization.IsLocalRepOn.suppAt_eq⟧: $\operatorname{supp}(\Lambda)(x) = \{s_1(x), \dots, s_k(x)\}$ for $x \in O$. If $w = s_i(x)$ then $\Lambda(w) \ge \sigma_i > 0$. Conversely, if $\Lambda(w) > 0$ the sum defining $\Lambda(w)$ is nonempty, so $w = s_i(x)$ for some $i$.
2. *Finite* ⟦Chapter13/MultisectionSupport · SBLocalization.IsScPlusMultisection.finite_suppAt⟧: from 1, at most $k$ elements.
3. *The weights over a point sum to $1$* ⟦Chapter13/MultisectionSupport · SBLocalization.IsScPlusMultisection.sum_suppAt⟧ ⟦Chapter13/MultisectionSupport · SBLocalization.IsScPlusMultisection.finsum_suppAt⟧. Group the indices $i$ by the value $s_i(x)$: $\sum_{w \in \operatorname{supp}(\Lambda)(x)}\Lambda(w) = \sum_w\sum_{i : s_i(x) = w}\sigma_i = \sum_i\sigma_i = 1$.
4. *Nonempty* ⟦Chapter13/MultisectionSupport · SBLocalization.IsScPlusMultisection.suppAt_nonempty⟧: an empty sum is $0 \neq 1$.
5. *Domain support as a closure* ⟦Chapter13/MultisectionSupport · SBLocalization.domSupp_eq_closure_image⟧: $\operatorname{dom-supp}(\Lambda) = \operatorname{cl}P(\operatorname{supp}(\Lambda) \setminus 0_W)$, which is the definition rewritten.

**Definition 13.2.3** (restated), p. 608 ⟦Chapter13/MultisectionSupport · SBLocalization.pointwiseNorm⟧. For an auxiliary norm $N$ on $W_{0,1}$ (Definition 8.3.5, Part VIII), the pointwise norm is $N(\Lambda)(x) = \max\{N(w) : w \in \operatorname{supp}(\Lambda)(x)\}$.
- $N$ is read on all of $W$ by setting it $0$ off $W_{0,1}$ ⟦Chapter13/MultisectionSupport · SBLocalization.normW⟧. The values of sc⁺-sections, and so the support, lie in $W_{0,1}$ ⟦Chapter13/MultisectionSupport · SBLocalization.IsScPlusMultisection.suppAt_subset_oneSet⟧, where $N$ is the given norm.
- The maximum is written as a supremum. It is attained ⟦Chapter13/MultisectionSupport · SBLocalization.IsScPlusMultisection.isGreatest_pointwiseNorm⟧, because the support over $x$ is finite and nonempty (2 and 4 above).
- For an auxiliary norm, $\operatorname{dom-supp}(\Lambda) = \operatorname{cl}\{x : N(\Lambda)(x) > 0\}$ ⟦Chapter13/MultisectionSupport · SBLocalization.IsScPlusMultisection.domSupp_eq_closure_pointwiseNorm⟧. $N(\Lambda)(x) > 0$ iff some $w \in \operatorname{supp}(\Lambda)(x)$ has $N(w) > 0$, iff some such $w$ is not $0_x$, since an auxiliary norm vanishes exactly at $0$ ⟦Chapter13/MultisectionSupport · SBLocalization.normW_eq_zero_iff⟧.

*Restated*: the maximum of the text is a supremum shown to be a maximum, and $N$ is extended by $0$ off $W_{0,1}$, where it is never evaluated on the support.

**Definition 13.2.4** (same), p. 609 ⟦Chapter13/MultisectionSupport · SBLocalization.IsTrivialOn⟧. $\Lambda$ is trivial on $V$ if $\Lambda(0_x) = 1$ for all $x \in V$.
- The text's "and hence $\Lambda(w) = 0$ for $w \neq 0_x$" is proved: $\Lambda(0_x) = 1$ iff $\Lambda(w) = 0$ for all $w \neq 0_x$ in $W_x$ ⟦Chapter13/MultisectionSupport · SBLocalization.IsScPlusMultisection.apply_fiberZero_eq_one_iff⟧, because the weights over $x$ sum to $1$ (3 above).
- $\operatorname{dom-supp}(\Lambda)$ is the smallest closed set off which $\Lambda$ is trivial ⟦Chapter13/MultisectionSupport · SBLocalization.IsScPlusMultisection.isLeast_domSupp⟧.
  - Off $\operatorname{dom-supp}(\Lambda)$ no $w \neq 0$ has positive weight, so $\Lambda$ is trivial there.
  - If $\Lambda$ is trivial off a closed $C$, then every $x$ with some $w \neq 0_x$, $\Lambda(w) > 0$, lies in $C$, and so does the closure of the set of such $x$.
- The *zero multisection* has $\Lambda(0_x) = 1$ and $\Lambda(w) = 0$ for $w \neq 0$. It is an sc⁺-multisection, with the zero section of weight $1$, and it is trivial everywhere ⟦Chapter13/MultisectionSupport · SBLocalization.isTrivialOn_zeroMultisection⟧. It is the witness for every notion of this section.

### XIII.9 Definition 13.2.5 (2017: Definition 13.8) and Lemma 13.2.6 (2017: Lemma 13.3): symmetric structures

**Transported sections** ⟦Chapter13/MultisectionSymmetric · SBLocalization.transportSection⟧. For a map $\tau$ from objects to morphisms and a map $b$ from objects to $W$ with $P(b(z)) = s(\tau(z))$, the transported section is $z \mapsto \mu(\tau(z), b(z))$. It is an sc⁺-section on $U$ when:
- $\tau$ is sc-smooth on $U$;
- $b$ is sc⁺ along $s \circ \tau$;
- $t(\tau(z)) = z$

⟦Chapter13/MultisectionSymmetric · SBLocalization.isScPlusSectionOn_transportSection⟧. The action $\mu$ is an sc-smooth strong bundle map on the fibred product (Chapter 8, Part VIII), and it preserves the $(0,1)$-level. Every construction in this chapter that moves a section along morphisms is a transported section.

**Definition 13.2.5** (restated), p. 610 ⟦Chapter13/MultisectionSymmetric · SBLocalization.SymmetricStructure⟧. A symmetric structure of $\Lambda$ at $x$ consists of:
- the domain $U(x)$ of a natural representation of $G_x$ with the properness property;
- a finite index set $I_x$ with an action of $G_x$;
- sc⁺-sections $s_i$ on $U(x)$, $i \in I_x$, with
  - (1) $s_{g(i)}(g * y) = \mu(\Gamma(g, y), s_i(y))$ for $y \in U(x)$;
  - (2) $\Lambda(w) = |I_x|^{-1}\#\{i : s_i(P(w)) = w\}$ for $P(w) \in U(x)$.

*Restated*: "$G_x$-invariant with the natural action" is read as the domain of a natural representation, the reading of Chapter 11. The index set lives in the universe of the isotropy groups. The version on neighbourhoods with the natural action, which the good systems need, is below.

**Equal weights** ⟦Chapter13/MultisectionSymmetric · SBLocalization.IsLocalRepOn.exists_equal_weights⟧. A local section structure $(s_i, \sigma_i)_{i \le k}$ on $O$ can be rewritten with all weights equal.
1. Write $\sigma_i = n_i/d_i$ and $p = \prod_jd_j$.
2. Set $m_i = n_i\prod_{j \neq i}d_j$, so $\sigma_i = m_i/p$.
3. Take the index type $\coprod_i\{1, \dots, m_i\}$, the section $s_i$ on each of the $m_i$ copies, and the common weight $1/p$.
4. The count is unchanged: $\sum_{(i,r) : s_i = w}1/p = \sum_{i : s_i = w}m_i/p$.

The total number of indices is $\sum_im_i = p\sum_i\sigma_i = p$. This is the text's $k_jq$.

**Lemma 13.2.6** (same), p. 610 ⟦Chapter13/MultisectionSymmetric · SBLocalization.lemma_13_2_6⟧. Every sc⁺-multisection has a symmetric structure at every point. The proof is the text's, before Definition 13.2.5.
1. *A local structure on a natural domain.*
   - Take a local section structure $(s_i, \sigma_i)$ on an open $O \ni x$.
   - Take a natural representation of $G_x$ with the properness property on a domain $U \subset O$ (Theorem 7.1.13 with the properness property, Part VII).
   - Restrict the structure to $U$ and extend the sections by $0$ off $U$ (§XIII.8).
2. *Equal weights.* Rewrite with equal weights $1/p$ on an index type $I_1$ with $|I_1| = p$.
3. *Symmetrize.*
   - Let $\hat I = I_1 \times G_x$, with $h \cdot (j, g) = (j, hg)$ ⟦Chapter13/MultisectionSymmetric · SBLocalization.prodIsotropyAction⟧.
   - Let $S_{(j,g)}(z) = \mu(\Gamma(g, g^{-1} * z), t_j(g^{-1} * z))$, the section $t_j$ moved by $g$: the transported section with $\tau(z) = \Gamma(g, g^{-1} * z)$, whose target is $z$.
   - These are sc⁺ on $U$ ⟦Chapter13/MultisectionSymmetric · SBLocalization.isScPlusSectionOn_transportSection⟧, since $\Phi(g^{-1})$ and $\Gamma(g, \cdot)$ are sc-smooth.
4. *Equivariance (1).* We need $S_{(j,hg)}(h * z) = \mu(\Gamma(h, z), S_{(j,g)}(z))$.
   - The left side is $\mu(\Gamma(hg, g^{-1} * z), t_j(g^{-1} * z))$.
   - By $\Gamma(hg, u) = \Gamma(h, g * u) \circ \Gamma(g, u)$ with $u = g^{-1} * z$, and the composition law $\mu(\psi \circ \chi, w) = \mu(\psi, \mu(\chi, w))$, this is the right side.
5. *The count (2).* Fix $w$ with $P(w) = z \in U$.
   - For each $g$, let $w_g = \mu(\Gamma(g, g^{-1} * z)^{-1}, w)$, a vector over $g^{-1} * z$.
   - $\mu(\Gamma(g, \cdot), \cdot)$ is a bijection of fibres, so $S_{(j,g)}(z) = w$ iff $t_j(g^{-1} * z) = w_g$.
   - $\Lambda$ is a functor, so $\Lambda(w_g) = \Lambda(w)$. By the equal-weight structure, $\#\{j : t_j(g^{-1} * z) = w_g\} = p\Lambda(w)$.
   - Summing over the $|G_x|$ values of $g$: $\#\{(j, g) : S_{(j,g)}(z) = w\} = |G_x|p\Lambda(w) = |\hat I|\Lambda(w)$.

**Neighbourhoods with the same action** ⟦Chapter13/SymmetricOn · EpGroupoid.NatNbhd.Le⟧. For two neighbourhoods $N_1$, $N_2$ of $x$ with the natural action, $N_1 \le N_2$ means:
- $U_1 \subset U_2$;
- $\Gamma_1(g, z) = \Gamma_2(g, z)$ for $z \in U_1$, hence also $\Phi_1(g) = \Phi_2(g)$ on $U_1$.

It is reflexive and transitive. Two neighbourhoods with the same natural representation are comparable.

*A common refinement* ⟦Chapter13/SymmetricOn · EpGroupoid.NatNbhd.exists_le_of_finite⟧. Given a neighbourhood $N_0$, finitely many neighbourhoods $N_1, \dots, N_m$ of $x$ with the natural action, and an open $V \ni x$, there is $M \le N_0$, $M \le N_i$ for all $i$, with $U_M \subset V$ and the representation of $N_0$.
1. Two natural representations of $G_x$ agree on the connected component of $x$ in the intersection of their domains, by the uniqueness of natural representations (Theorem 7.1.13, Part VII).
2. The component of $x$ in the open set $U_{R_0} \cap \bigcap_iU_{R_i}$ is open, by local connectedness.
3. On it all the $\Gamma_i$ agree with $\Gamma_0$.
4. The invariant core (§XIII.1) of $N_0$ inside this component, intersected with $V$ and all $U_i$, is the required $M$.

This lemma is what makes the intersections in Definitions 13.2.9 and 13.2.12 meaningful.

**Moving vectors along morphisms** ⟦Chapter13/SymmetricOn · SBLocalization.fibAct⟧. $\mu(\psi, v)$ is written for $v$ over $s(\psi)$, and set to $v$ otherwise, so that it is a total function. It lands over $t(\psi)$ and maps $0$ to $0$. It is additive and homogeneous on sections:
- $\mu(\psi, s_1 + s_2) = \mu(\psi, s_1) + \mu(\psi, s_2)$ ⟦Chapter13/SymmetricOn · SBLocalization.fibAct_sectionAdd⟧;
- $\mu(\psi, \beta s) = \beta\mu(\psi, s)$ ⟦Chapter13/SymmetricOn · SBLocalization.fibAct_sectionSmul⟧;
- $\mu(\psi, \sum_ls_l) = \sum_l\mu(\psi, s_l)$ ⟦Chapter13/SymmetricOn · SBLocalization.fibAct_sectionSum⟧,

because $\mu(\psi, \cdot)$ is a linear isomorphism of fibres (Definition 8.3.1, Part VIII). These identities make every new family below equivariant and compatible with correspondences.

**Symmetric structures on a neighbourhood with the natural action** ⟦Chapter13/SymmetricOn · SBLocalization.SymmetricStructureOn⟧. This is Definition 13.2.5 on a neighbourhood $N$ of §XIII.1 instead of a natural domain. It consists of:
- a finite index type $I$ with a $G_x$-action;
- sc⁺-sections $s_i$ on $U$, equivariant through $\Gamma$ of $N$;
- the counting formula over $U$.

Its first properties:
- $I \neq \emptyset$ ⟦Chapter13/SymmetricOn · SBLocalization.SymmetricStructureOn.card_pos⟧. Over $x$ the support of $\Lambda$ is nonempty (§XIII.8), and a nonempty count needs an index.
- $|I|^{-1}$ summed over $I$ is $1$.
- *Where $\Lambda(0_y) = 1$ all sections vanish at $y$* ⟦Chapter13/SymmetricOn · SBLocalization.SymmetricStructureOn.s_eq_fiberZero⟧. The count of $0_y$ is $|I|^{-1}\#\{i : s_i(y) = 0_y\} = 1$, so every $i$ counts. The tight structures (§XIII.17) and the atomic structures (§XIII.26) use this.
- *Restriction* ⟦Chapter13/SymmetricOn · SBLocalization.SymmetricStructureOn.restrict⟧. A structure on $N$ restricts to any $M \le N$, with the same index set and sections. Equivariance needs that $\Gamma$ of $M$ is $\Gamma$ of $N$ on $U_M$, which is what $\le$ says.
- The structures of Definition 13.2.5 are structures on the neighbourhood given by their domain ⟦Chapter13/SymmetricOn · SBLocalization.SymmetricStructure.toOn⟧. So by Lemma 13.2.6 they exist at every point ⟦Chapter13/SymmetricOn · SBLocalization.exists_symmetricStructureOn⟧.

The algebra of structures is §§XIII.11–XIII.13.

### XIII.10 Definitions 13.2.7 and 13.2.8 (2017: Definitions 13.9 and 13.10): decorated sc⁺-multisections

**Good systems with smaller sets.** The decorations need good systems whose neighbourhoods are smaller than a given system's and whose natural actions may be different representations. ⟦Chapter13/DecoratedMultisection · EpGroupoid.GoodSystem.ofSubset⟧: if $(M(x))$ are neighbourhoods with the natural action, with $U_M(x) \subset U(x)$ for a good system $\mathcal U$, then $(M(x))$ is a good system.
- Properness passes to closed subsets.
- Condition (3) passes to subsets, as in Proposition 13.1.3.

The proof of Proposition 13.1.3 does not use that the representations are the same.

For two good systems there is a third inside both ⟦Chapter13/DecoratedMultisection · EpGroupoid.GoodSystem.exists_subset_inter⟧. At each $x$ the invariant core of $U_1(x)$ in $U_1(x) \cap U_2(x)$ is a neighbourhood with the natural action of the first system, and the previous lemma applies.

**Definition 13.2.7** (same), p. 610 ⟦Chapter13/DecoratedMultisection · SBLocalization.Decoration⟧ ⟦Chapter13/DecoratedMultisection · SBLocalization.DecoratedTuple⟧. A decoration of an sc⁺-multisection $\Lambda$ is a pair $(\mathcal U, S)$:
- $\mathcal U$ is a good system;
- for every $x$, $S(x)$ is a symmetric structure of $\Lambda$ on the neighbourhood $U(x)$.

A decorated tuple is $(\Lambda, \mathcal U, S)$ with $\Lambda$ an sc⁺-multisection. The properness clause of Definition 13.2.5 is Definition 13.1.2 (1), and the natural action is the good system's (§XIII.1).

*Existence* ⟦Chapter13/DecoratedMultisection · SBLocalization.exists_decoration⟧. Every sc⁺-multisection over an ep-groupoid with paracompact orbit space has a decoration.
1. At each $x$ take a symmetric structure $S_0(x)$ on a neighbourhood $N(x)$ (Lemma 13.2.6).
2. Theorem 13.1.8 gives a good system $\mathcal U_0$ with $U_0(x) \subset U_{N(x)}$.
3. At each $x$ take, by the common refinement lemma of §XIII.9, $M(x) \le N_0(x)$ and $M(x) \le N(x)$. On $M(x)$ the actions of the good system and of the structure agree.
4. $(M(x))$ is a good system by the lemma above, and $S_0(x)$ restricts to $M(x)$.

The paracompactness is the text's: the text's §13.2 assumes it through Theorem 13.1.8. It is witnessed as in the intro.

**Definition 13.2.8** (same), p. 611 ⟦Chapter13/DecoratedMultisection · SBLocalization.Decoration.Rel⟧. $(\Lambda, \mathcal U, S) \sim (\Lambda', \mathcal U', S')$ if:
- $\Lambda = \Lambda'$;
- there is a good system $\mathcal U''$ with $U''(x) \subset U(x) \cap U'(x)$ for all $x$;
- there are $G_x$-equivariant bijections $b_x : I_x \to I'_x$ with $s'_{b_x(i)} = s_i$ on $U''(x)$.

Equivariance of $b_x$ is with respect to the actions of the two structures. On $U''(x)$ these are the actions of the respective neighbourhoods. The definition does not ask that the two representations agree; the bijection and the sections carry the comparison.

*An equivalence relation.*
- Reflexive with $\mathcal U'' = \mathcal U$ and the identity ⟦Chapter13/DecoratedMultisection · SBLocalization.Decoration.Rel.refl⟧.
- Symmetric with the inverse bijections ⟦Chapter13/DecoratedMultisection · SBLocalization.Decoration.Rel.symm⟧.
- Transitive ⟦Chapter13/DecoratedMultisection · SBLocalization.Decoration.Rel.trans⟧: given $\mathcal U''_{12}$ and $\mathcal U''_{23}$, take a good system inside both (the lemma above) and compose the bijections. On the common system both equalities of sections hold.

So it is an equivalence ⟦Chapter13/DecoratedMultisection · SBLocalization.DecoratedTuple.equivalence⟧. Its classes are the decorated sc⁺-multisections ⟦Chapter13/DecoratedMultisection · SBLocalization.DecoratedMultisection⟧, with the map to the underlying functor ⟦Chapter13/DecoratedMultisection · SBLocalization.DecoratedMultisection.forget⟧, whose image consists of sc⁺-multisections.

### XIII.11 Definition 13.2.9 (2017: Definition 13.11) and the remark that there are no inverses: sums

**Convolution** ⟦Chapter13/MultisectionConvolution · SBLocalization.convAt⟧ ⟦Chapter13/MultisectionConvolution · SBLocalization.conv⟧. For finitely many functions $\Lambda_1, \dots, \Lambda_n : W \to \mathbb Q^+$ and $w \in W_x$,
$$(\ast_i\Lambda_i)(w) = \sum_{(w_1, \dots, w_n) \in W_x^n,\ \sum_iw_i = w}\ \prod_i\Lambda_i(w_i).$$
The sum is formally over all tuples in the fibre, as a sum with finite support. It is finite when each $\Lambda_i$ has finite support over $x$, which is the case for sc⁺-multisections (§XIII.8). The algebra of §13.2 consists of this one operation.

*Expansion of a product of sums.* If each $\Lambda_i$ is given on $O$ by a local structure $(s^i_j, \sigma^i_j)_{j \in J_i}$, then for $P(w) \in O$
$$(\ast_i\Lambda_i)(w) = \sum_{(j_1, \dots, j_n) : \sum_is^i_{j_i}(P(w)) = w}\ \prod_i\sigma^i_{j_i}$$
⟦Chapter13/MultisectionConvolution · SBLocalization.conv_eq_sum_of_isLocalRepOn⟧.
1. Substitute $\Lambda_i(w_i) = \sum_{j : s^i_j = w_i}\sigma^i_j$ into the convolution.
2. Expand the product of sums as a sum over tuples $(j_1, \dots, j_n)$, distributivity over a product of finite sums.
3. Exchange the sums. For a fixed tuple $(j_i)$ the inner sum over $(w_i)$ has the single term $w_i = s^i_{j_i}$, present iff $\sum_is^i_{j_i} = w$.

*A local structure for the convolution* ⟦Chapter13/MultisectionConvolution · SBLocalization.isLocalRepOn_conv⟧. On $O$, the sections $\sum_is^i_{j_i}$, indexed by tuples, are sc⁺ (sums, §XIII.8), and the weights $\prod_i\sigma^i_{j_i}$ are positive and sum to $\prod_i\sum_j\sigma^i_j = 1$.

*A functor* ⟦Chapter13/MultisectionConvolution · SBLocalization.isWFunctor_conv⟧. $\mu(\varphi, \cdot)$ is a linear isomorphism $W_x \to W_{x'}$, so it maps the decompositions of $w$ bijectively to the decompositions of $\mu(\varphi, w)$. Each factor keeps its value, the $\Lambda_i$ being functors.

*An sc⁺-multisection* ⟦Chapter13/MultisectionConvolution · SBLocalization.isScPlusMultisection_conv⟧. At each point, intersect the domains of local structures of the $\Lambda_i$ and use the local structure above.

**Definition 13.2.9 for functors.** The sum $\Lambda' \oplus \Lambda''(w) = \sum_{w' + w'' = w}\Lambda'(w')\Lambda''(w'')$ is the text's formula (1) ⟦Chapter13/MultisectionAlgebra · SBLocalization.multisectionAdd⟧. It is the convolution of the pair, through the identification of pairs with functions on a two-element set ⟦Chapter13/MultisectionAlgebra · SBLocalization.multisectionAdd_eq_conv⟧.
- So it is an sc⁺-multisection ⟦Chapter13/MultisectionAlgebra · SBLocalization.definition_13_2_9⟧.
- Locally it is given by the sections $s'_i + s''_j$ with weights $\sigma'_i\sigma''_j$ on a common domain ⟦Chapter13/MultisectionAlgebra · SBLocalization.multisectionAdd_eq_sum_of_isLocalRepOn⟧, which is the text's (2)–(3) at the level of local structures.
- *Commutative* for all functions ⟦Chapter13/MultisectionAlgebra · SBLocalization.multisectionAdd_comm⟧, by swapping the two summands of a decomposition.
- *Associative* on sc⁺-multisections ⟦Chapter13/MultisectionAlgebra · SBLocalization.multisectionAdd_assoc⟧. Both sides are sums over decompositions $w = w_1 + w_2 + w_3$ with weight $\Lambda_1(w_1)\Lambda_2(w_2)\Lambda_3(w_3)$, exchanged as finite sums because the fibre supports are finite.
- *The zero multisection is neutral* ⟦Chapter13/MultisectionNoInverse · SBLocalization.multisectionAdd_zeroMultisection⟧. In $\Lambda \oplus \Lambda_0(w)$ only the decomposition $w = w + 0$ contributes.

**Definition 13.2.9 for decorations** (restated), p. 611 ⟦Chapter13/DecoratedMultisection · SBLocalization.definition_13_2_9_decorated⟧. Given decorations $(\mathcal U', S')$ of $\Lambda'$ and $(\mathcal U'', S'')$ of $\Lambda''$, the decoration of $\Lambda' \oplus \Lambda''$ ⟦Chapter13/DecoratedMultisection · SBLocalization.Decoration.add⟧ has:
- *Neighbourhoods* inside $U'(x) \cap U''(x)$ ⟦Chapter13/DecoratedMultisection · SBLocalization.Decoration.add_U_subset⟧, chosen by the common refinement lemma of §XIII.9 so that the actions of $U'(x)$ and $U''(x)$ agree on them ⟦Chapter13/DecoratedMultisection · SBLocalization.Decoration.exists_common⟧. They form a good system, by the lemma of §XIII.10.
- *Index sets* $I'_x \times I''_x$ with the diagonal action ⟦Chapter13/DecoratedMultisection · SBLocalization.Decoration.add_I⟧.
- *Sections* $s_{(i,i')} = s'_i + s''_{i'}$ ⟦Chapter13/DecoratedMultisection · SBLocalization.Decoration.add_s_apply⟧.

*Reading.* The text takes $U(x) = U'(x) \cap U''(x)$. The two natural actions on it need not agree. A symmetric structure needs one action for which both families are equivariant, and Definition 13.1.2 needs one natural representation. So $U(x)$ is an open neighbourhood of $x$ inside the intersection on which the two actions agree. The class does not depend on this choice, since Definition 13.2.8 allows shrinking.

*The symmetric structure of the sum* ⟦Chapter13/SymmetricOn · SBLocalization.SymmetricStructureOn.add⟧.
- *Sc⁺:* sums of sc⁺-sections.
- *Equivariance:* $s'_{gi}(g * y) + s''_{gi'}(g * y) = \mu(\Gamma, s'_i(y)) + \mu(\Gamma, s''_{i'}(y)) = \mu(\Gamma, s'_i(y) + s''_{i'}(y))$, by additivity of $\mu(\psi, \cdot)$.
- *The count:* $|I' \times I''|^{-1}\#\{(i, i') : s'_i + s''_{i'} = w\}$ is the expansion of the convolution with weights $|I'|^{-1}|I''|^{-1}$, so it equals $\Lambda' \oplus \Lambda''(w)$.

*Well defined on classes* ⟦Chapter13/DecoratedMultisection · SBLocalization.Decoration.add_rel⟧. If $(\Lambda', \mathcal U'_1, S'_1) \sim (\Lambda', \mathcal U'_2, S'_2)$ with bijections $b'_x$ on $\mathcal U'_{12}$, and likewise for $\Lambda''$, then the sums are equivalent. Use a good system inside all four neighbourhood systems and the two common ones, and the product bijections $b'_x \times b''_x$.

So $\oplus$ is defined on decorated sc⁺-multisections ⟦Chapter13/DecoratedMultisection · SBLocalization.DecoratedMultisection.add⟧, compatibly with forgetting ⟦Chapter13/DecoratedMultisection · SBLocalization.DecoratedMultisection.forget_add⟧. It is commutative ⟦Chapter13/DecoratedMultisection · SBLocalization.DecoratedMultisection.add_comm⟧ and associative ⟦Chapter13/DecoratedMultisection · SBLocalization.DecoratedMultisection.add_assoc⟧ there, through the swap bijection $I' \times I'' \to I'' \times I'$ ⟦Chapter13/DecoratedMultisection · SBLocalization.Decoration.add_comm_rel⟧ and the reassociation bijection of triple products ⟦Chapter13/DecoratedMultisection · SBLocalization.Decoration.add_assoc_rel⟧.

**The remark after Definition 13.2.9: no inverses** (same), p. 611. "Inverse" is read with respect to the neutral element $\Lambda_0$, the zero multisection.
1. *The example.*
   - Take the trivial bundle $\mathbb R^n \times \mathbb R^k \to \mathbb R^n$ over the trivial ep-groupoid $\mathbb R^n$ ⟦Chapter13/MultisectionNoInverse · SBLocalization.NoInverse.A⟧.
   - For a constant $c \in \mathbb R^k$, let $\Lambda_c$ give weight $\tfrac12$ to the zero section and $\tfrac12$ to the constant section $c$ ⟦Chapter13/MultisectionNoInverse · SBLocalization.NoInverse.twoValued⟧. When $c \neq 0$, $\Lambda_c(0) = \Lambda_c(c) = \tfrac12$.
   - It is an sc⁺-multisection ⟦Chapter13/MultisectionNoInverse · SBLocalization.NoInverse.isScPlusMultisection_twoValued⟧, with that two-section local structure everywhere. Constant sections of a trivial bundle are sc⁺.
2. *Two values have total weight at most $1$* ⟦Chapter13/MultisectionNoInverse · SBLocalization.NoInverse.add_le_one_of_ne⟧. For an sc⁺-multisection $\Lambda'$ and $u \neq v$ in one fibre, $\Lambda'(u) + \Lambda'(v) \le 1$, because the weights over a point sum to $1$ (§XIII.8).
3. *No inverse* ⟦Chapter13/MultisectionNoInverse · SBLocalization.NoInverse.remark_13_2_9_no_inverse⟧. For $c \neq 0$ and every sc⁺-multisection $\Lambda'$, $\Lambda_c \oplus \Lambda' \neq \Lambda_0$.
   - Over $x = 0$, the decompositions $0 = w' + w''$ with $\Lambda_c(w') > 0$ are $w' = 0$ and $w' = c$.
   - So $(\Lambda_c \oplus \Lambda')(0_x) = \tfrac12\Lambda'(0) + \tfrac12\Lambda'(-c) \le \tfrac12$, by step 2 with $0 \neq -c$.
   - But $\Lambda_0(0_x) = 1$.
4. *Such a $\Lambda_c$ exists* when $k \ge 1$ ⟦Chapter13/MultisectionNoInverse · SBLocalization.NoInverse.exists_no_inverse⟧, with $c$ the constant vector with all entries $1$.

### XIII.12 Definition 13.2.10 (2017: Definition 13.12) and Lemma 13.2.11 (2017: Lemma 13.4): multiples and products with functions

**Definition 13.2.10 for functors** (same), p. 611 ⟦Chapter13/MultisectionAlgebra · SBLocalization.multisectionSmul⟧. For $a \in \mathbb R$:
- $(0 \cdot \Lambda)(0_x) = 1$ and $(0 \cdot \Lambda)(w) = 0$ for $w \neq 0_x$;
- $(a\Lambda)(w) = \Lambda(a^{-1}w)$ for $a \neq 0$.

Facts:
- $0 \cdot \Lambda$ is the zero multisection ⟦Chapter13/MultisectionAlgebra · SBLocalization.multisectionSmul_zero⟧.
- $a\Lambda$ is a functor: $\mu(\varphi, \cdot)$ is linear, so $\mu(\varphi, a^{-1}w) = a^{-1}\mu(\varphi, w)$.
- If $\Lambda$ is given on $O$ by $(s_i, \sigma_i)$, then $a\Lambda$ is given on $O$ by $(as_i, \sigma_i)$ ⟦Chapter13/MultisectionAlgebra · SBLocalization.multisectionSmul_eq_sum_of_isLocalRepOn⟧.
  - For $a \neq 0$: $as_i(P(w)) = w$ iff $s_i(P(w)) = a^{-1}w$.
  - For $a = 0$: all sections $as_i$ are $0$. The sum of all weights is $1$ at $w = 0$ and the empty sum is $0$ at $w \neq 0$, which is the zero multisection.
- The sections $as_i$ are sc⁺ (constant multiples, §XIII.8). So $a\Lambda$ is an sc⁺-multisection ⟦Chapter13/MultisectionAlgebra · SBLocalization.definition_13_2_10⟧.

**Lemma 13.2.11 for functors** (same), p. 612 ⟦Chapter13/MultisectionAlgebra · SBLocalization.lemma_13_2_11⟧. Let $\beta : X \to \mathbb R$ be an sc-smooth functor: sc-smooth on the objects and constant along morphisms, $\beta(t\varphi) = \beta(s\varphi)$. Define $(\beta\Lambda)(w) = (\beta(P(w))\Lambda)(w)$ ⟦Chapter13/MultisectionAlgebra · SBLocalization.multisectionSmulFun⟧. Then $\beta\Lambda$ is an sc⁺-multisection.
1. *A functor.* For $\varphi$ with $P(w) = s\varphi$: $(\beta\Lambda)(\mu(\varphi, w)) = (\beta(t\varphi)\Lambda)(\mu(\varphi, w)) = (\beta(s\varphi)\Lambda)(\mu(\varphi, w)) = (\beta(s\varphi)\Lambda)(w)$, using the invariance of $\beta$ and the functoriality of $\beta(s\varphi)\Lambda$.
2. *Local structure.* Near a point, take $(s_i, \sigma_i)$ for $\Lambda$ on $O$. The sections $\beta s_i$ are sc⁺ on $O$ ($\beta$ sc-smooth, §XIII.8). With the weights $\sigma_i$ they represent $\beta\Lambda$, by the pointwise formula of Definition 13.2.10 at $a = \beta(P(w))$.
3. No case distinction is needed between $\beta \neq 0$ and $\beta = 0$. The local formula of Definition 13.2.10 holds for every $a$, including $0$, and is applied pointwise.

**Decorated versions** (same). The decoration of $a\Lambda$ ⟦Chapter13/DecoratedMultisection · SBLocalization.Decoration.smul⟧ ⟦Chapter13/DecoratedMultisection · SBLocalization.definition_13_2_10_decorated⟧ keeps the good system and index sets and multiplies the sections by $a$.
- Equivariance is homogeneity of $\mu(\psi, \cdot)$ (§XIII.9).
- The count is the local formula above, with all weights $|I_x|^{-1}$.
- For $a = 0$ the sections are $0$ and the count gives the zero multisection.

The decoration of $\beta\Lambda$ ⟦Chapter13/DecoratedMultisection · SBLocalization.Decoration.smulFun⟧ ⟦Chapter13/DecoratedMultisection · SBLocalization.lemma_13_2_11_decorated⟧ has the sections $\beta s_i$. Equivariance of $\beta s_i$ uses $\beta(g * y) = \beta(y)$, which is the invariance of $\beta$ along $\Gamma(g, y)$, together with homogeneity of $\mu$.

Both are compatible with Definition 13.2.8 ⟦Chapter13/DecoratedMultisection · SBLocalization.Decoration.smulFun_rel⟧, with the same bijections. So they are defined on decorated classes ⟦Chapter13/DecoratedMultisection · SBLocalization.DecoratedMultisection.smul⟧.

### XIII.13 Definition 13.2.12 (2017: Definition 13.13) and Lemma 13.2.13 (2017: Lemma 13.5): locally finite sums

**Definition 13.2.12** (same), p. 612 ⟦Chapter13/MultisectionLocallyFinite · SBLocalization.IsLocallyFiniteFamily⟧. A family $(\Lambda_j)_{j \in J}$ of functions $W \to \mathbb Q^+$ is locally finite if every $x$ has an open saturated $O(x) \ni x$ for which the set
$$J_{O(x)} = \{j : \exists w \neq 0,\ P(w) \in O(x),\ \Lambda_j(w) > 0\}$$
⟦Chapter13/MultisectionLocallyFinite · SBLocalization.nontrivIdx⟧ is finite.

*The remark after it* ⟦Chapter13/MultisectionLocallyFinite · SBLocalization.IsLocallyFiniteFamily.exists_stable⟧. $O(x)$ can be chosen so that the index set does not change on smaller open saturated neighbourhoods of $x$.
1. Among the open saturated $O \ni x$ with $J_O$ finite, choose one whose $J_O$ has the fewest elements, a minimum of natural numbers.
2. For a smaller open saturated $O' \ni x$, $J_{O'} \subset J_O$, and $J_{O'}$ is finite. By minimality it is not smaller, so $J_{O'} = J_O$.

**Lemma 13.2.13 for functors** (restated), p. 612 ⟦Chapter13/MultisectionLocallyFinite · SBLocalization.lemma_13_2_13⟧. The sum of a locally finite family of sc⁺-multisections is an sc⁺-multisection.

*The sum written out* ⟦Chapter13/MultisectionLocallyFinite · SBLocalization.lfSum⟧. The text writes $\bigoplus_{j \in J}\Lambda_j$ without a formula for infinite $J$. It is read as
$$\Big(\bigoplus_j\Lambda_j\Big)(w) = \sum_{(w_j) \text{ finitely supported},\ \sum_jw_j = w}\ \prod_j\Lambda_j(w_j),$$
where the product over $j$ is over the finitely many $j$ with $w_j \neq 0$, each other factor $\Lambda_j(0)$ being read as $1$ near the point. For finite $J$ this is the convolution of §XIII.11 ⟦Chapter13/MultisectionLocallyFinite · SBLocalization.lfSum_eq_conv⟧: a finitely supported family on a finite set is a function, and the identification is a bijection of index sets of the two sums.

*Proof.*
1. *Trivial members.* For $j \notin J_{O(x)}$ and $y \in O(x)$, $\Lambda_j$ is trivial at $y$. Its only positive value over $y$ is at $0_y$, with weight $1$ (§XIII.8).
2. *Over $O(x)$ the sum is a finite convolution* ⟦Chapter13/MultisectionLocallyFinite · SBLocalization.lfSum_eq_conv_of_mem⟧.
   - In a decomposition $(w_j)$ of $w$ over $y \in O(x)$, every $j \notin J_{O(x)}$ with $w_j \neq 0$ makes the product $0$.
   - So only decompositions supported in the finite set $J_{O(x)}$ contribute, and the factors of the other indices are $\Lambda_j(0) = 1$.
   - These are exactly the terms of the finite convolution over $J_{O(x)}$.
3. *A functor.* The saturated $O(x)$ contains both ends of every morphism leaving it. Along $\varphi$ the formula of step 2 is the finite convolution, which is a functor (§XIII.11).
4. *Local structure.* On $O(x)$ the finite convolution has the local structure of §XIII.11, intersected over the finitely many local structures of the $\Lambda_j$, $j \in J_{O(x)}$.

*Restated*: the infinite sum, left implicit in the text, is written out.

**Decorated version** (restated) ⟦Chapter13/DecoratedMultisection · SBLocalization.lemma_13_2_13_decorated⟧. Given decorations $(\mathcal U_j, S_j)$ of a locally finite family, and a good system $\mathcal U_0$, the decoration of $\bigoplus_j\Lambda_j$ ⟦Chapter13/DecoratedMultisection · SBLocalization.Decoration.lfSum⟧ has the following data at $x$.
- *Neighbourhood*: inside $O(x) \cap \bigcap_{j \in J_x}U_j(x)$, with $J_x = J_{O(x)}$. It is chosen by the common refinement lemma of §XIII.9 so that the natural actions of $\mathcal U_0$ and of all $U_j(x)$, $j \in J_x$, agree on it ⟦Chapter13/DecoratedMultisection · SBLocalization.exists_lfData⟧.
- *Index set* $\prod_{j \in J_x}I^j_x$, with sections $\sum_{j \in J_x}s^{j,x}_{i_j}$ ⟦Chapter13/DecoratedMultisection · SBLocalization.lfSumStructure⟧.
  - This is the symmetric structure of a finite product ⟦Chapter13/SymmetricOn · SBLocalization.SymmetricStructureOn.pi⟧, whose count is the expansion of §XIII.11.
  - It is then transferred to $\bigoplus_j\Lambda_j$ by step 2 above, since the count formula only depends on $\Lambda$ through its values on the neighbourhood.

*Reading.* The intersection is read as for Definition 13.2.9. When $J_x = \emptyset$, the text leaves the natural action on $O(x)$ open. It is taken from $\mathcal U_0$, an argument of the construction: any $\mathcal U_j$, or Theorem 13.1.8. With $J_x = \emptyset$ the index set is the empty product, a one-point set, and the section is the empty sum $0$, which represents the trivial sum.

### XIII.14 Definitions 13.3.1 and 13.3.2, Example 13.3.3, Definition 13.3.4 and Remark 13.3.5 (2017: Definitions 13.14 and 13.15, Example 13.1, Definition 13.16, Remark 13.1): correspondences

§13.3 opens with the display (13.5) on p. 613. It names, for two points $x$, $x'$ with symmetric structures, the finite index sets $I_x$ and $I_{x'}$ that the correspondences relate. The formalization has no separate statement for it. Its content is the setting of Definition 13.3.1.

**Definition 13.3.1** (same), p. 613 ⟦Chapter13/Correspondence · SBLocalization.IndexDiagram⟧. A diagram $I_x \xleftarrow{a} I \xrightarrow{b} I_{x'}$ of finite sets with:
- $a$ and $b$ surjective;
- all fibres of $a$ of one size;
- all fibres of $b$ of one size.

The fibre sizes are compared through cardinalities of subtypes. Two diagrams are equivalent if a bijection $c : I \to I'$ makes both triangles commute ⟦Chapter13/Correspondence · SBLocalization.IndexDiagram.Equiv⟧. This is an equivalence relation ⟦Chapter13/Correspondence · SBLocalization.IndexDiagram.equivalence⟧, and $J(x, x')$ is the set of classes, the *correspondences* ⟦Chapter13/Correspondence · SBLocalization.IndexCorr⟧.

Constructions on classes:
- A bijection $e : I_x \to I_{x'}$ gives $[I_x \xleftarrow{\mathrm{id}} I_x \xrightarrow{e} I_{x'}]$. The special case $e : I_x \to I_x$ a permutation by $g \in G_x$ is written $[\mathrm{id}, g]$ ⟦Chapter13/Correspondence · SBLocalization.IndexCorr.ofPerm⟧.
- Relabelling the two outer sets by bijections acts on classes ⟦Chapter13/Correspondence · SBLocalization.IndexCorr.map⟧. It is well defined because an equivalence $c$ of diagrams is also one of the relabelled diagrams.

**Definition 13.3.2** (stronger), p. 614.
- *The pseudo-inverse* $\sharp$ reverses a diagram, $[a, b]^\sharp = [b, a]$ ⟦Chapter13/Correspondence · SBLocalization.IndexCorr.swap⟧. It is an involution ⟦Chapter13/Correspondence · SBLocalization.IndexCorr.swap_swap⟧, so a bijection $J(x, x') \to J(x', x)$ ⟦Chapter13/Correspondence · SBLocalization.IndexCorr.swapEquiv⟧.
- *The bi-action* is $g' * [a, b] * g = [g^{-1} \circ a, g' \circ b]$ ⟦Chapter13/Correspondence · SBLocalization.IndexCorr.biact⟧, written as the relabelling by the permutations $g^{-1}$ and $g'$.
- *Stronger*: the text defines the maps; the formalization also proves the action laws, which the text does not state:
  - $1 * \tau * 1 = \tau$ ⟦Chapter13/Correspondence · SBLocalization.IndexCorr.biact_one_one⟧;
  - $g' * (h' * \tau * h) * g = (g'h') * \tau * (hg)$ ⟦Chapter13/Correspondence · SBLocalization.IndexCorr.biact_biact⟧.

  This is an action of $G_{x'} \times G_x^{\mathrm{op}}$, the same shape as the bi-action on morphisms (§XIII.3). It is what Definition 13.3.4 (2) compares with.

**Example 13.3.3** (same), p. 614 ⟦Chapter13/Correspondence · SBLocalization.IndexCorr.example_13_3_3⟧. If $I_x = \{*\}$, then $g' * \tau * g = \tau$ for all $g$, $g'$.
1. $a$ is constant, so $g^{-1} \circ a = a$.
2. For $g' \circ b$, build a bijection $c : I \to I$ with $b \circ c = g' \circ b$ fibre by fibre. The fibre $b^{-1}(j)$ and the fibre $b^{-1}(g'^{-1}j)$ have the same size, so there is a bijection between them. Assembling these bijections gives a bijection of $I$, with $a \circ c = a$ trivially.

**Definition 13.3.4** (same), p. 614 ⟦Chapter13/StructurableMultisection · SBLocalization.Decoration.IsCorrespondence⟧. For a decoration $(\mathcal U, S)$ and points $x$, $x'$, a map $\tau$ from morphisms to $J(x, x')$ is a correspondence if on $\mathcal U(x, x')$:
- (1) it is locally constant and has finitely many values on $\mathcal U(x, x')$;
- (2) it is equivariant: $\tau(g' * \varphi * g) = g' * \tau(\varphi) * g$, with the bi-action of the good system (§XIII.3) on the left and that of Definition 13.3.2 on the right, for the actions of the symmetric structures on the index sets;
- (3) it is compatible with the sections: for every representative $I_x \xleftarrow{a} I \xrightarrow{b} I_{x'}$ of $\tau(\varphi)$, every $k \in I$ and every $\psi$ in the component of $\varphi$ in $\mathcal U(x, x')$,
$$s^{x'}_{b(k)}(t\psi) = \mu(\psi, s^x_{a(k)}(s\psi))$$
⟦Chapter13/StructurableMultisection · SBLocalization.Decoration.Compat⟧.

$\tau$ is a function on all morphisms; only its values on $\mathcal U(x, x')$ enter.

**Remark 13.3.5** (same), p. 615 ⟦Chapter13/Correspondence · SBLocalization.IndexCorr.sat_iff⟧. For a relation $R$ on $I_x \times I_{x'}$, "$R(a(k), b(k))$ for all $k \in I$" is invariant under equivalence of diagrams ⟦Chapter13/Correspondence · SBLocalization.IndexDiagram.sat_iff_of_equiv⟧: the bijection $c$ only renames $k$. So it is a property of the class ⟦Chapter13/Correspondence · SBLocalization.IndexCorr.Sat⟧, held by $\tau$ iff by one representative iff by every representative. Condition (3) is of this form. The text's remark, that (3) does not depend on the representative, is this lemma.

The saturation property has the expected closure properties, used below:
- it passes to products, relabellings and $\sharp$;
- it is monotone in $R$;
- it holds for every $R$ that holds everywhere.

### XIII.15 Definitions 13.3.6–13.3.11 and Remarks 13.3.7, 13.3.9 (2017: Definitions 13.17–13.20, Remarks 13.2, 13.3): structurable and structured sc⁺-multisections

**Definition 13.3.6** (same), p. 615 ⟦Chapter13/StructurableMultisection · SBLocalization.Decoration.Tau⟧. A *structure* on a decoration $(\mathcal U, S)$ is a family of correspondences $\tau_{x,x'}$, for all $x$, $x'$, with:
- (1) $\tau_{x,x}(\Gamma(g, y)) = [\mathrm{id}, g]$ for $y \in U(x)$, $g \in G_x$;
- (2) $\tau_{x',x}(\varphi) = \tau_{x,x'}(\varphi^{-1})^\sharp$ for $\varphi \in \mathcal U(x', x)$.

A function $\Lambda$ is *structurable* if it is an sc⁺-multisection and some decoration of it carries a structure ⟦Chapter13/StructurableMultisection · SBLocalization.IsStructurable⟧. A decorated class is structurable if a representative carries one ⟦Chapter13/StructurableMultisection · SBLocalization.DecoratedMultisection.IsStructurable⟧. The two notions agree: $\Lambda$ is structurable iff it underlies a structurable decorated class ⟦Chapter13/StructurableMultisection · SBLocalization.isStructurable_iff⟧.

*The witness*, the zero multisection ⟦Chapter13/StructurableMultisection · SBLocalization.isStructurable_zeroMultisection⟧, over an ep-groupoid with a good system:
- at every point the index set $\{*\}$ with the zero section, which is a symmetric structure of the zero multisection;
- every $\tau_{x,x'}$ the unit diagram $[\{*\} \leftarrow \{*\} \to \{*\}]$.

Conditions (1)–(2) hold because, on one-point sets, every correspondence is the unit diagram (Example 13.3.3), and (3) holds because both sides are zero. The good system is from Theorem 13.1.8, so the witness is stated over a paracompact orbit space.

**Remark 13.3.7 and Definition 13.3.8** (same), p. 616. The tuples $(\Lambda, \mathcal U, S, \tau)$ ⟦Chapter13/StructurableMultisection · SBLocalization.StructuredTuple⟧ are compared ⟦Chapter13/StructurableMultisection · SBLocalization.StructuredTuple.Equiv⟧ as follows. $(\Lambda, \mathcal U, S, \tau) \sim (\Lambda', \mathcal U', S', \tau')$ if:
- $\Lambda = \Lambda'$;
- there is a good system $\mathcal U''$ with $U''(x) \subset U(x) \cap U'(x)$;
- $I_x = I'_x$ for all $x$;
- $\tau = \tau'$ on $\mathcal U''(x, x')$.

The equality of index sets is an equality of types, and $\tau'$ is compared with $\tau$ after transport along it. This is an equivalence relation ⟦Chapter13/StructurableMultisection · SBLocalization.StructuredTuple.equivalence⟧. For transitivity, use a good system inside both intermediate ones (§XIII.10) and compose the type equalities. Its classes are the *structured sc⁺-multisections* ⟦Chapter13/StructurableMultisection · SBLocalization.StructuredMultisection⟧.

*Reading.* As printed, Definition 13.3.8 puts no condition on the sections $S$, $S'$. It is formalized as printed. Nothing in this chapter uses the sections of an equivalent tuple: every construction on classes is shown independent of the representative through $\Lambda$, the good systems and $\tau$. The face analogue in Theorem 14.6.3 does use them: its proof on p. 682 states the equality of the sections of equivalent tuples, and the formal Theorem 14.6.3 takes that equality as part of the equivalence; with Definition 13.3.8 alone it does not hold as we read it (Part XIV, §XIV.28). Remark 13.3.7 says the structures are what makes sums well defined; this is §XIII.16.

**Remark 13.3.9** (nothing), p. 616: prose on the role of the structures. It has no formal counterpart.

**Definition 13.3.10** (same), p. 616: structured sc⁺-multisections are the classes above, and the forgetful map to sc⁺-multisections is $[\Lambda, \mathcal U, S, \tau] \mapsto \Lambda$.

**Definition 13.3.11** (same), p. 617.
- $\Gamma^+_m(P)$, the sc⁺-multisections ⟦Chapter13/StructurableMultisection · SBLocalization.Γm⟧;
- $\Gamma^+_s(P)$, the structurable ones ⟦Chapter13/StructurableMultisection · SBLocalization.Γs⟧;
- $\Gamma^+_{st}(P)$, the structured ones ⟦Chapter13/StructurableMultisection · SBLocalization.Γst⟧.

$\Gamma^+_s \subset \Gamma^+_m$, and the forgetful map sends $\Gamma^+_{st}$ onto $\Gamma^+_s$ ⟦Chapter13/StructurableMultisection · SBLocalization.StructuredMultisection.range_forget⟧. This is the text's statement that every structurable $\Lambda$ lifts to a structured one: a structurable $\Lambda$ has a decoration with a structure, whose class lies over $\Lambda$.

### XIII.16 Proposition 13.3.12 (2017: Proposition 13.3), Remark 13.3.13 (2017: Remark 13.4) and Lemma 13.3.14 (2017: Lemma 13.6): sums and multiples of structurable sc⁺-multisections

**The product of two correspondences** ⟦Chapter13/Correspondence · SBLocalization.IndexCorr.prod⟧. $[a_1, b_1] \times [a_2, b_2] = [a_1 \times a_2, b_1 \times b_2]$, a diagram $I^1_x \times I^2_x \leftarrow I_1 \times I_2 \to I^1_{x'} \times I^2_{x'}$.
- The fibres of a product map are products of fibres ⟦Chapter13/Correspondence · SBLocalization.IndexDiagram.card_fiber_prodMap⟧, so they have equal sizes. Products of surjections are surjective.
- The product is well defined on classes, by the product of the equivalences.
- It commutes with $\sharp$ ⟦Chapter13/Correspondence · SBLocalization.IndexCorr.prod_swap⟧, with the bi-action for the diagonal actions ⟦Chapter13/Correspondence · SBLocalization.IndexCorr.prod_biact⟧, and with $[\mathrm{id}, g]$ ⟦Chapter13/Correspondence · SBLocalization.IndexCorr.prod_ofPerm⟧.
- A product saturates the product relation when each factor saturates its relation.

**Proposition 13.3.12** (restated), p. 617 ⟦Chapter13/StructurableMultisection · SBLocalization.proposition_13_3_12⟧. The sum of two structurable sc⁺-multisections is structurable.

*Proof.*
1. *"We may assume $\mathcal U_1 = \mathcal U_2$."* Let $\Lambda_1$, $\Lambda_2$ carry structures $\tau^1$, $\tau^2$ over decorations $(\mathcal U_1, S_1)$, $(\mathcal U_2, S_2)$. The decorated sum (§XIII.11) has neighbourhoods $M(x)$ with $M(x) \le N_1(x)$ and $M(x) \le N_2(x)$.
   - Both structures restrict to the decorations on $(M(x))$ ⟦Chapter13/StructurableMultisection · SBLocalization.Decoration.Tau.restrict⟧.
   - On smaller neighbourhoods, $\mathcal U_M(x, x') \subset \mathcal U_i(x, x')$ and the components are smaller, so local constancy and compatibility restrict.
   - The bi-action does not change on a smaller neighbourhood with the same action ⟦Chapter13/StructurableMultisection · EpGroupoid.GoodSystem.biact_congr_of_le⟧, because it is built from the $\Gamma$'s, which agree there. So equivariance restricts.
   - The diagonal condition (1) holds because $\Gamma$ is the same.
2. *The structure of the sum* ⟦Chapter13/StructurableMultisection · SBLocalization.Decoration.Tau.prod⟧ ⟦Chapter13/StructurableMultisection · SBLocalization.Decoration.Tau.add⟧ is $\tau = \tau^1 \times \tau^2$ on the index sets $I^1_x \times I^2_x$ with sections $s^1_i + s^2_j$.
   - *Local constancy:* both factors are locally constant near $\varphi$.
   - *Finiteness:* the values lie in the product of two finite sets of values.
   - *Equivariance:* factorwise, through the product lemma for the bi-action.
   - *(1) and (2) of Definition 13.3.6:* factorwise, through the product lemmas for $[\mathrm{id}, g]$ and $\sharp$.
   - *Compatibility (3):* the text's computation. For representatives with $s^1_{b_1(k)} = \mu(\psi, s^1_{a_1(k)})$ and $s^2_{b_2(l)} = \mu(\psi, s^2_{a_2(l)})$, $\mu(\psi, s^1_{a_1(k)} + s^2_{a_2(l)}) = s^1_{b_1(k)} + s^2_{b_2(l)}$, by additivity of $\mu(\psi, \cdot)$ (§XIII.9).
3. For structured tuples the sum is again a structured tuple ⟦Chapter13/StructurableMultisection · SBLocalization.StructuredTuple.add⟧, over $\Lambda_1 \oplus \Lambda_2$ ⟦Chapter13/StructurableMultisection · SBLocalization.StructuredTuple.add_Λ⟧.

*Restated*: "we may assume $\mathcal U_1 = \mathcal U_2$" is carried out by restriction to the neighbourhoods of the decorated sum, on which the two natural actions agree.

**Remark 13.3.13** (narrower), p. 618. The structured sums $\Lambda_1 \oplus \Lambda_2$ and $\Lambda_2 \oplus \Lambda_1$ have the same underlying functor. This is `StructuredTuple.add_Λ` with the commutativity of §XIII.11. The remark's negative half is that the two differ as structured classes, since the index sets are $I^1_x \times I^2_x$ and $I^2_x \times I^1_x$. That is a statement that two types are unequal, and it has no formal statement (§XIII.31).

**Lemma 13.3.14** (same), p. 618 ⟦Chapter13/StructurableMultisection · SBLocalization.lemma_13_3_14⟧ ⟦Chapter13/StructurableMultisection · SBLocalization.lemma_13_3_14_fun⟧. If $\Lambda$ is structurable, so is $r\Lambda$ for every $r \in \mathbb R$, including $0$, and so is $\beta\Lambda$ for every sc-smooth functor $\beta$.
- The same $\tau$ serves ⟦Chapter13/StructurableMultisection · SBLocalization.Decoration.Tau.smul⟧ ⟦Chapter13/StructurableMultisection · SBLocalization.Decoration.Tau.smulFun⟧, on the decorations of §XIII.12.
- Compatibility (3) is homogeneity: $\mu(\psi, rs_{a(k)}) = r\mu(\psi, s_{a(k)}) = rs_{b(k)}$.
- For $\beta$, additionally $\beta(t\psi) = \beta(s\psi)$.
- Conditions (1), (2) and equivariance do not involve the sections.

### XIII.17 The construction before Proposition 13.3.15, Proposition 13.3.15, Remark 13.3.16, Definition 13.3.17 and Corollary 13.3.18 (2017: Proposition 13.4, Remark 13.5, Definition 13.21, Corollary 13.1): tight structures

**The trivial set $T_\Lambda$** ⟦Chapter13/TightMultisection · SBLocalization.trivialSet⟧. The set of points $y$ that have an open neighbourhood on which $\Lambda$ is trivial (Definition 13.2.4).
- It is open ⟦Chapter13/TightMultisection · SBLocalization.isOpen_trivialSet⟧.
- $\Lambda$ is trivial on it ⟦Chapter13/TightMultisection · SBLocalization.isTrivialOn_trivialSet⟧.
- Triviality at $s(\psi)$ and at $t(\psi)$ are the same: $\Lambda(0_{t\psi}) = \Lambda(\mu(\psi, 0_{s\psi})) = \Lambda(0_{s\psi})$, $\Lambda$ being a functor ⟦Chapter13/TightMultisection · SBLocalization.apply_fiberZero_tgt⟧. For a neighbourhood, transport by a sheet of $t$.

**The construction** (stronger), pp. 618–619. Let $(\Lambda, \mathcal U, S, \tau)$ be a structured tuple.
1. *Neighbourhoods.* For $x \in T_\Lambda$, shrink $U(x)$ to a neighbourhood with the same action inside $U(x) \cap T_\Lambda$ ⟦Chapter13/TightMultisection · SBLocalization.Decoration.exists_tightNbhd⟧ ⟦Chapter13/TightMultisection · SBLocalization.Decoration.tightNbhd⟧. This is the common refinement lemma of §XIII.9 with an empty family and $V = T_\Lambda$. For $x \notin T_\Lambda$ keep $U(x)$.
2. *Index sets.* One type that is $\{*\}$ when $x \in T_\Lambda$ and $I_x$ otherwise ⟦Chapter13/TightMultisection · SBLocalization.TightIdx⟧: the sum of $\{*\}$ restricted to "$x \in T_\Lambda$" and $I_x$ restricted to "$x \notin T_\Lambda$". There are bijections $\{*\} \simeq I'_x$ when $x \in T_\Lambda$ ⟦Chapter13/TightMultisection · SBLocalization.TightIdx.eT⟧ and $I_x \simeq I'_x$ when $x \notin T_\Lambda$ ⟦Chapter13/TightMultisection · SBLocalization.TightIdx.eN⟧. The text's equalities $I'_x = \{*\}$, $I'_x = I_x$ are these bijections. The $G_x$-action and the sections are carried along them: the zero section on $\{*\}$, the old ones on $I_x$. Counts are invariant under such relabelling.
3. *The decoration* ⟦Chapter13/TightMultisection · SBLocalization.Decoration.tight⟧. On $\{*\}$ the zero section represents $\Lambda$ on $U'(x) \subset T_\Lambda$, because $\Lambda$ is trivial there.
4. *The correspondences* ⟦Chapter13/TightMultisection · SBLocalization.Decoration.tightτ⟧, by the four cases for $(x, x')$:
   - both in $T_\Lambda$: the unit diagram, relabelled;
   - $x \in T_\Lambda$, $x' \notin T_\Lambda$: $[\{*\} \leftarrow I_{x'} \xrightarrow{\mathrm{id}} I_{x'}]$, relabelled ⟦Chapter13/TightMultisection · SBLocalization.Decoration.tightτ_TN⟧;
   - $x \notin T_\Lambda$, $x' \in T_\Lambda$: $[I_x \xleftarrow{\mathrm{id}} I_x \to \{*\}]$, relabelled;
   - neither: the old $\tau_{x,x'}$, relabelled by $e_x$, $e_{x'}$ ⟦Chapter13/TightMultisection · SBLocalization.Decoration.tightτ_NN⟧.

**It is again structured** (stronger) ⟦Chapter13/TightMultisection · SBLocalization.Decoration.Tau.tight⟧.
1. *Constant correspondences are correspondences*, as far as (1)–(2) of Definition 13.3.4 go ⟦Chapter13/TightMultisection · SBLocalization.Decoration.isCorrespondence_const⟧. A constant is locally constant with one value. For equivariance, a diagram with one outer set a point and the other mapped by the identity is fixed by the bi-action, by Example 13.3.3 and its mirror image.
2. *Relabelling commutes with $\sharp$ and the bi-action* ⟦Chapter13/TightMultisection · SBLocalization.IndexCorr.swap_map⟧ ⟦Chapter13/TightMultisection · SBLocalization.IndexCorr.biact_map⟧, so the case "neither" inherits (1)–(2) and conditions (1)–(2) of Definition 13.3.6 from $\tau$. Relabelling the unit diagram by $\{*\} \simeq I'_x$ commutes with permutations.
3. *Compatibility (3)* is the step the text does not check. At a morphism $\psi$ in a component of $\mathcal U'(x, x')$ with $x \in T_\Lambda$ or $x' \in T_\Lambda$:
   - $s\psi \in U'(x)$ and $t\psi \in U'(x')$, and one of these lies in $T_\Lambda$. Triviality passes along $\psi$, so $\Lambda(0) = 1$ at both ends.
   - Every section of a symmetric structure vanishes where $\Lambda(0_y) = 1$ (§XIII.9). So all sections at both ends are $0$ at the relevant points.
   - Both sides of (3) are $0$, since $\mu(\psi, 0) = 0$.
4. *Diagonal (1) of Definition 13.3.6* for $x \in T_\Lambda$: $[\mathrm{id}, g]$ on a point is the unit diagram. For $x \notin T_\Lambda$ it is $\tau$'s, relabelled.

**Proposition 13.3.15** (restated), p. 619 ⟦Chapter13/TightMultisection · SBLocalization.proposition_13_3_15⟧. From a structured representative $(\Lambda, \mathcal U, S, \tau)$ one gets a structured $(\Lambda, \mathcal U', S', \tau')$ with:
- (1) for $x \in T_\Lambda$: $I'_x = \{*\}$ with the zero section, and $U'(x) \subset T_\Lambda$ with the action of $U(x)$;
- (2) for $x \notin T_\Lambda$: $U'(x) = U(x)$, and equivariant bijections $e_x : I_x \to I'_x$ with $s'_{e_x(i)} = s_i$;
- (3) $\tau'$ is $\tau$ relabelled by $e_x$, $e_{x'}$, for $x, x' \notin T_\Lambda$;
- (4)–(5) the unit-type diagrams otherwise.

It is the construction above ⟦Chapter13/TightMultisection · SBLocalization.Decoration.isTight_tight⟧. Condition (3) holds for all morphisms, not only on $\mathcal U'(x, x')$. *Restated*: the equalities of index sets are the bijections of step 2.

**Remark 13.3.16** (nothing), p. 619: prose. No formal counterpart.

**Definition 13.3.17** (same), p. 620 ⟦Chapter13/TightMultisection · SBLocalization.Decoration.IsTight⟧ ⟦Chapter13/TightMultisection · SBLocalization.StructuredMultisection.IsTight⟧. A structured representative is tight if:
- (1) $I_x = \{*\}$ with the zero section for $x \in T_\Lambda$;
- (2) $\tau_{x,x'}$ is $[* \leftarrow I_{x'} \xrightarrow{\mathrm{id}} I_{x'}]$, resp. $[I_x \xleftarrow{\mathrm{id}} I_x \to *]$, when exactly one of $x$, $x'$ lies in $T_\Lambda$;
- (3) $[\{*\} \leftarrow \{*\} \to \{*\}]$ when both do.

"$I_x = \{*\}$" is a bijection $\{*\} \simeq I_x$, and (2)–(3) are stated for every such bijection. All are equal, since a one-point set has one bijection to a given one-point set. A structured class is tight if one representative is.

**Corollary 13.3.18** (same), p. 620 ⟦Chapter13/TightMultisection · SBLocalization.corollary_13_3_18⟧ ⟦Chapter13/TightMultisection · SBLocalization.corollary_13_3_18_structured⟧. Every structurable $\Lambda$ has a tightly structured version, and every element of $\Gamma^+_s$ underlies a tightly structured class. This is Proposition 13.3.15 applied to a structure of $\Lambda$.

### XIII.18 Proposition 13.3.19 (2017: Proposition 13.5): locally finite sums of structurable sc⁺-multisections

The text proves Proposition 13.3.19 (p. 620) in a paragraph, and leaves to the reader the check that the product of infinitely many correspondences is well defined. The formalization writes that check out. It needs three tools: products of families of correspondences, tight versions over a common good system, and the bookkeeping that near two given points only finitely many factors are not the unit.

**Products of families of correspondences** ⟦Chapter13/PiCorrespondence · SBLocalization.IndexCorr.pi⟧. Let $(\tau^l)_{l \in L}$ be correspondences, $\tau^l \in J(I^l, I'^l)$.
- *On diagrams* ⟦Chapter13/PiCorrespondence · SBLocalization.IndexDiagram.pi⟧, the product of $I^l \xleftarrow{a_l} M^l \xrightarrow{b_l} I'^l$ is $\prod_lI^l \leftarrow \prod_lM^l \to \prod_lI'^l$. It is a diagram when $\prod_lM^l$ is finite. The fibres of a product map are products of fibres, so all fibres have one size ⟦Chapter13/PiCorrespondence · SBLocalization.IndexDiagram.card_fiber_pi⟧.
- *On classes*, the product is taken through chosen representatives ⟦Chapter13/PiCorrespondence · SBLocalization.IndexCorr.out⟧. Any family of representatives gives the same class ⟦Chapter13/PiCorrespondence · SBLocalization.IndexCorr.pi_eq_mk⟧: the product of the equivalences is an equivalence. So equal factors give equal products ⟦Chapter13/PiCorrespondence · SBLocalization.IndexCorr.pi_congr⟧.
- *Finiteness.* A product of finite types that are one-point outside a finite set is finite ⟦Chapter13/PiCorrespondence · SBLocalization.finite_pi_of_subsingleton⟧. A correspondence equal to a diagram with one-point middle set has one-point middle set in its chosen representative ⟦Chapter13/PiCorrespondence · SBLocalization.IndexCorr.subsingleton_out_I⟧, since equivalent diagrams have bijective middle sets.
- *Laws.*
  - The product saturates the conjunction of relations when every factor saturates its relation ⟦Chapter13/PiCorrespondence · SBLocalization.IndexCorr.sat_pi⟧.
  - It commutes with $\sharp$ ⟦Chapter13/PiCorrespondence · SBLocalization.IndexCorr.swap_pi⟧ and with the bi-action of the isotropy groups acting factorwise ⟦Chapter13/PiCorrespondence · SBLocalization.IndexCorr.biact_pi⟧.
  - The product of the diagrams $[\mathrm{id}, g]$ is $[\mathrm{id}, g]$ for the product action ⟦Chapter13/PiCorrespondence · SBLocalization.IndexCorr.pi_ofPerm⟧.
- *Reindexing.* A symmetric structure can be relabelled along an equivariant bijection of index sets ⟦Chapter13/PiCorrespondence · SBLocalization.SymmetricStructureOn.reindex⟧.
- *Additivity.* $\mu(\psi, \cdot)$ is additive over finite sums of vectors ⟦Chapter13/PiCorrespondence · SBLocalization.fibAct_sum⟧.

**Tight versions over a given good system.** The tight version of §XIII.17 lives on the decoration's own good system. The sum needs tight versions of all members over one common good system. A good system $\mathcal U$ is *adapted* to a structured decoration $(\mathcal U_\Lambda, S, \tau)$ of $\Lambda$ ⟦Chapter13/TightOn · SBLocalization.Decoration.IsAdapted⟧ if:
- $U(x) \subset T_\Lambda$ for $x \in T_\Lambda$;
- for $x \notin T_\Lambda$, the neighbourhood $U(x)$ is $\le U_\Lambda(x)$, the same action on a smaller set.

Over an adapted system:
- *The tight structure* ⟦Chapter13/TightOn · SBLocalization.SymmetricStructureOn.tightRel⟧ has index set $\{*\}$ with the zero section at $x \in T_\Lambda$, and $I_x$ with the restricted sections at $x \notin T_\Lambda$. The decoration is ⟦Chapter13/TightOn · SBLocalization.Decoration.tightOn⟧.
- *The correspondences* ⟦Chapter13/TightOn · SBLocalization.Decoration.tightOnτ⟧ are the given $\tau$ between points outside $T_\Lambda$, and the unit-type diagrams otherwise, as in §XIII.17. They form a structure ⟦Chapter13/TightOn · SBLocalization.Decoration.Tau.tightOn⟧ by the argument of §XIII.17. Compatibility at the trivial points is again the vanishing of all sections where $\Lambda(0) = 1$.
- *It is tight* (Definition 13.3.17) ⟦Chapter13/TightOn · SBLocalization.Decoration.isTight_tightOn⟧.

**The data of the proof** ⟦Chapter13/LocallyFiniteStructurable · SBLocalization.LFStructData⟧ consist of:
- the members $\Lambda_l$, $l \in L$, sc⁺-multisections;
- the local finiteness of Definition 13.2.12;
- decorations $(\mathcal U^l, S^l)$ with structures $\tau^l$;
- a good system $\mathcal U_0$, which provides the natural actions at points where no member is nontrivial.

The index type $L$ lives in the universe of the bundle.

**The common good system.**
1. *$O(x)$ and $F(x)$* ⟦Chapter13/LocallyFiniteStructurable · SBLocalization.LFStructData.O⟧ ⟦Chapter13/LocallyFiniteStructurable · SBLocalization.LFStructData.F⟧. For each $x$, $O(x)$ is the open saturated set of Definition 13.2.12. $F(x)$ is the finite set of members nontrivial over $O(x)$; it contains the text's $J_x$. For $l \notin F(x)$, $O(x) \subset T_{\Lambda_l}$ ⟦Chapter13/LocallyFiniteStructurable · SBLocalization.subset_trivialSet_of_not_mem_nontrivIdx⟧: an open set over which no $w \neq 0$ has positive weight is a set on which $\Lambda_l$ is trivial (§XIII.8).
2. *$V(x)$* ⟦Chapter13/LocallyFiniteStructurable · SBLocalization.LFStructData.V⟧. $V(x) = O(x) \cap \bigcap_{l \in F(x),\ x \in T_{\Lambda_l}}T_{\Lambda_l}$, open, containing $x$. This is the text's "$V(x) \subset T_l$".
3. *$M(x)$* ⟦Chapter13/LocallyFiniteStructurable · SBLocalization.LFStructData.exists_M⟧ ⟦Chapter13/LocallyFiniteStructurable · SBLocalization.LFStructData.M⟧. A neighbourhood with the representation of $\mathcal U_0$ at $x$, inside $V(x)$, with $M(x) \le U_0(x)$ and $M(x) \le U^l(x)$ for all $l \in F(x)$. This is the common refinement lemma of §XIII.9 for the finitely many $U^l(x)$, $l \in F(x)$. It is the text's $U(x) = V(x) \cap \bigcap_{l \in J_x}U^l(x)$, shrunk so that the natural actions agree.
4. *The good system* ⟦Chapter13/LocallyFiniteStructurable · SBLocalization.LFStructData.𝒰⟧ is $(M(x))$, by the lemma of §XIII.10 applied inside $\mathcal U_0$.
5. *Adapted to every member* ⟦Chapter13/LocallyFiniteStructurable · SBLocalization.LFStructData.isAdapted⟧. These are properties (3)–(4) of the text's proof.
   - If $x \in T_{\Lambda_l}$: either $l \in F(x)$, and $M(x) \subset V(x) \subset T_{\Lambda_l}$ by step 2; or $l \notin F(x)$, and $M(x) \subset O(x) \subset T_{\Lambda_l}$ by step 1.
   - If $x \notin T_{\Lambda_l}$: then $l \in F(x)$, by step 1, and $M(x) \le U^l(x)$ by step 3.
6. *Tight versions* ⟦Chapter13/LocallyFiniteStructurable · SBLocalization.LFStructData.Dt⟧ ⟦Chapter13/LocallyFiniteStructurable · SBLocalization.LFStructData.tt⟧ of all members over $\mathcal U$. For $l \notin F(x)$, the tight index set at $x$ is a point and its section is $0$.

**The symmetric structure of the sum.**
1. *The index set* $K_x = \prod_{l \in L}K^l_x$, with $K^l_x$ the tight index set of $\Lambda_l$ at $x$ ⟦Chapter13/LocallyFiniteStructurable · SBLocalization.LFStructData.K⟧. It is finite ⟦Chapter13/LocallyFiniteStructurable · SBLocalization.LFStructData.finite_K⟧: all factors with $l \notin F(x)$ are points.
2. *The base structure* ⟦Chapter13/LocallyFiniteStructurable · SBLocalization.LFStructData.baseS⟧ is the locally finite sum structure of §XIII.13 over the finite set $F(x)$, with index set $\prod_{l \in F(x)}K^l_x$.
3. *Restriction to $F(x)$ is a bijection* $K_x \to \prod_{l \in F(x)}K^l_x$ ⟦Chapter13/LocallyFiniteStructurable · SBLocalization.LFStructData.res_bijective⟧. It is injective because the other factors are points, and surjective by extending with the unique point.
4. *The structure* $s^x$ ⟦Chapter13/LocallyFiniteStructurable · SBLocalization.LFStructData.Sx⟧ is the base structure relabelled along that bijection. The decoration of $\bigoplus_l\Lambda_l$ is $(\mathcal U, s)$ ⟦Chapter13/LocallyFiniteStructurable · SBLocalization.LFStructData.Dsum⟧.
5. *The text's formula* ⟦Chapter13/LocallyFiniteStructurable · SBLocalization.LFStructData.Sx_s_apply⟧: $s^x_k(y) = \sum_{l \in T}s^{l,x}_{k(l)}(y)$ for every finite $T \supset F(x)$. The terms with $l \notin F(x)$ are zero sections ⟦Chapter13/LocallyFiniteStructurable · SBLocalization.tightIdx_elim_zero⟧. This independence of $T$ is what the compatibility below needs: at a morphism from $U(x)$ to $U(x')$ both structures are written over $T = F(x) \cup F(x')$.

**The correspondences.**
1. *Unit factors.* For $l \notin F(x) \cup F(x')$, both $x$ and $x'$ lie in $T_{\Lambda_l}$, so $\tau^l_{x,x'}$ is the relabelled unit diagram, the same for every morphism ⟦Chapter13/LocallyFiniteStructurable · SBLocalization.LFStructData.τ_TT⟧.
2. *The product is defined* ⟦Chapter13/LocallyFiniteStructurable · SBLocalization.LFStructData.finite_out⟧. The middle sets of the chosen representatives are points outside the finite $F(x) \cup F(x')$, so their product is finite.
3. *The correspondence* $\tau_{x,x'}(\varphi) = \prod_{l \in L}\tau^l_{x,x'}(\varphi)$ ⟦Chapter13/LocallyFiniteStructurable · SBLocalization.LFStructData.τ⟧. It depends only on the finitely many factors in $F(x) \cup F(x')$ ⟦Chapter13/LocallyFiniteStructurable · SBLocalization.LFStructData.τ_congr⟧.

**Definition 13.3.4 for the product** ⟦Chapter13/LocallyFiniteStructurable · SBLocalization.LFStructData.isCorrespondence⟧.
1. *Locally constant.* Each of the finitely many relevant factors is locally constant near $\varphi$, so they are simultaneously constant near $\varphi$, and the product is too.
2. *Finitely many values.* If $\mathcal U(x, x')$ is empty there is nothing to show. Otherwise the tuple of relevant factors takes values in a finite product of finite sets. The product correspondence is a function of that tuple, so it takes finitely many values.
3. *Equivariance.* Factorwise, by the product law for the bi-action.
4. *Compatibility.* The product of the factors' saturations saturates the conjunction (the product law for saturation). Given the conjunction for indices $k$, $k'$, the sum formula with $T = F(x) \cup F(x')$ and additivity of $\mu(\psi, \cdot)$ give $s^{x'}_{k'}(t\psi) = \sum_l s^{l,x'}_{k'(l)}(t\psi) = \sum_l\mu(\psi, s^{l,x}_{k(l)}(s\psi)) = \mu(\psi, s^x_k(s\psi))$.

**Definition 13.3.6 for the product** ⟦Chapter13/LocallyFiniteStructurable · SBLocalization.LFStructData.tau⟧.
- *Diagonal:* the product of $[\mathrm{id}, g]$ is $[\mathrm{id}, g]$.
- *Swap:* the product of the swaps is the swap of the product; the finiteness of the swapped product is again by the unit factors.

This is the step left to the reader.

**Proposition 13.3.19** (restated), p. 620 ⟦Chapter13/LocallyFiniteStructurable · SBLocalization.proposition_13_3_19⟧. For a nonempty family of structurable sc⁺-multisections, locally finite in the sense of Definition 13.2.12, the sum $\bigoplus_l\Lambda_l$ is structurable. The data above give the structure ⟦Chapter13/LocallyFiniteStructurable · SBLocalization.LFStructData.isStructurable⟧, with Lemma 13.2.13 for the sc⁺-multisection property. For a nonempty family the good system $\mathcal U_0$ is taken from any member's structure.
- For any family, including the empty one, given a good system ⟦Chapter13/LocallyFiniteStructurable · SBLocalization.proposition_13_3_19_of_goodSystem⟧.
- For any family over a paracompact $|X|$, through Theorem 13.1.8 ⟦Chapter13/LocallyFiniteStructurable · SBLocalization.proposition_13_3_19_of_paracompact⟧.

The sum over the empty family is the zero multisection, which is structurable exactly when a good system exists, as Definition 13.3.6 requires. *Added hypothesis*: for the empty family, the existence of a good system. It is not derived from the text, it is necessary, and its witness is Theorem 13.1.8.

**Locally finite domain supports** ⟦Chapter13/LocallyFiniteSupports · SBLocalization.isLocallyFiniteFamily_of_locallyFinite⟧. The text's hypothesis is that the domain supports form a locally finite family of subsets of $X$. It implies Definition 13.2.12 for families of functors.
1. For $x$ take an open $V \ni x$ meeting finitely many $\operatorname{dom-supp}(\Lambda_l)$, and $O = \pi^{-1}(\pi(V))$. It is open by Proposition 7.1.8 (Part VII), and saturated.
2. Suppose $\Lambda_l(w) > 0$ for some $w \neq 0$ over $y \in O$. Choose a morphism $\varphi : y \to v$ with $v \in V$.
3. $\mu(\varphi, w) \neq 0$ ⟦Chapter13/LocallyFiniteSupports · SBLocalization.μ_ne_fiberZero_lf⟧, since $\mu(\varphi, \cdot)$ is a linear isomorphism. Also $\Lambda_l(\mu(\varphi, w)) = \Lambda_l(w) > 0$.
4. So $v \in \operatorname{dom-supp}(\Lambda_l) \cap V$, and $l$ is one of the finitely many indices.

The saturation of the domain supports is not needed. So Proposition 13.3.19 holds with the hypothesis as printed ⟦Chapter13/LocallyFiniteSupports · SBLocalization.proposition_13_3_19_locallyFinite⟧, and for any family over a paracompact $|X|$ ⟦Chapter13/LocallyFiniteSupports · SBLocalization.proposition_13_3_19_locallyFinite_of_paracompact⟧.

*Restated*: the index sets $K_x$ are products of types relabelled by a bijection, and the structure is built over one adapted good system rather than "the same $\mathcal U$" the text takes. "Locally finite" is proved from the printed hypothesis.

### XIII.19 Theorem 13.4.1 (2017: Theorem 13.3): pull-back along a strong bundle equivalence

**The common data of a pull-back** ⟦Chapter13/StrongBundlePullMap · SBLocalization.PullMap⟧. Both Theorem 13.4.1 and Theorem 13.4.4 pull local sc⁺-section structures back along a map $\Phi : W \to W'$ covering a functor $F : X \to X'$. What the two proofs use of $\Phi$ is the same:
- $\Phi$ commutes with the actions: $\Phi(\mu(\varphi, w)) = \mu'(F(\varphi), \Phi(w))$;
- every point has an open neighbourhood over which $\Phi$ is a strong bundle isomorphism onto its image, over a local sc-diffeomorphism of the bases;
- $F$ is faithful: two morphisms with the same source, the same target and the same image agree.

Instances:
- A strong bundle equivalence (Definition 10.4.1, Part X) gives such data ⟦Chapter13/StrongBundlePullMap · SBLocalization.PullMap.ofEquivalence⟧. Its base is an equivalence, faithful by definition.
- A proper strong bundle covering, 2021 Definition 8.5.9, gives such data ⟦Chapter13/StrongBundlePullMap · SBLocalization.PullMap.ofCovering⟧. Faithfulness comes from Definition 8.5.1 (3): the map $\varphi \mapsto (F(\varphi), s(\varphi))$ is an sc-diffeomorphism onto the fibred product, so injective.

**Consequences of the data.**
- $P'(\Phi(w)) = F(P(w))$.
- On fibres, $\Phi$ is a linear homeomorphism $W_y \to W'_{F(y)}$ ⟦Chapter13/StrongBundlePullMap · SBLocalization.PullMap.fiberEquiv⟧. It is injective on fibres ⟦Chapter13/StrongBundlePullMap · SBLocalization.PullMap.eq_of_obj_eq⟧.
- $F$ is a local sc-diffeomorphism on objects ⟦Chapter13/StrongBundlePullMap · SBLocalization.PullMap.isLocalScDiffeo_obj⟧.
- $\Phi$ intertwines the actions in the total form of §XIII.9 ⟦Chapter13/StrongBundlePullMap · SBLocalization.PullMap.obj_fibAct⟧.

*Pulled-back sections* ⟦Chapter13/StrongBundlePullMap · SBLocalization.PullMap.pullSec⟧: $z \mapsto \Phi_z^{-1}(s'(F(z)))$, with $\Phi_z$ the fibre map. For an sc⁺-section $s'$ on $U'$ and an open $U$ with $F(U) \subset U'$, it is an sc⁺-section on $U$ ⟦Chapter13/StrongBundlePullMap · SBLocalization.PullMap.isScPlusSectionOn_pullSec⟧: near each point it is $s'$ composed with a local strong bundle isomorphism and the local sc-diffeomorphism $F$. It satisfies $\Phi(\text{pull}\ s'(z)) = s'(F(z))$, and $\text{pull}\ s'(z) = w$ iff $s'(F(z)) = \Phi(w)$ ⟦Chapter13/StrongBundlePullMap · SBLocalization.PullMap.pullSec_eq_iff⟧.

*The pulled-back functor* $\Phi^*\Lambda' = \Lambda' \circ \Phi$ ⟦Chapter13/StrongBundlePullMap · SBLocalization.PullMap.pull⟧ is a functor ⟦Chapter13/StrongBundlePullMap · SBLocalization.PullMap.isWFunctor_pull⟧: $\Lambda'(\Phi(\mu(\varphi, w))) = \Lambda'(\mu'(F\varphi, \Phi w)) = \Lambda'(\Phi w)$.

**$\Phi^*\Lambda'$ is an sc⁺-multisection** ⟦Chapter13/MultisectionPullback · SBLocalization.PullMap.isScPlusMultisection_pull⟧. A local structure $(s'_i, \sigma_i)$ of $\Lambda'$ on $O' \ni F(x)$ pulls back to $(\text{pull}\ s'_i, \sigma_i)$ on $F^{-1}(O')$ ⟦Chapter13/MultisectionPullback · SBLocalization.PullMap.exists_isLocalRepOn_pull⟧. By the last property of pulled-back sections, $\text{pull}\ s'_i(P(w)) = w$ iff $s'_i(F(P(w))) = \Phi(w)$, so the counts agree.

**Adapted neighbourhoods** ⟦Chapter13/MultisectionPullback · SBLocalization.PullMap.IsPullNbhd⟧. For a neighbourhood $N'$ of $F(x)$ with the natural action, a neighbourhood $N$ of $x$ is adapted if:
- $F$ is injective on $U$;
- $F(U) \subset U'$;
- $F(\Gamma(g, z)) = \Gamma'(F(g), F(z))$ for $z \in U$, with $F(g) \in G'_{F(x)}$ the image of $g$ under the isotropy homomorphism.

Then $F(g * z) = F(g) * F(z)$ ⟦Chapter13/MultisectionPullback · SBLocalization.PullMap.IsPullNbhd.Φ_eq⟧, applying $t$ to the identity.

*Existence inside every open $V \ni x$, with the properness property* ⟦Chapter13/MultisectionPullback · SBLocalization.PullMap.exists_isPullNbhd⟧.
1. $F$ is a local sc-diffeomorphism at $x$: there is an open $U_0 \ni x$ on which it is injective with a local inverse.
2. Let $O = V \cap U_0 \cap F^{-1}(U')$ and $N_0$ a neighbourhood of $x$ with the natural action and proper closure inside $O$ (§XIII.1).
3. Let $E$ be the set of $y \in U_0(N_0)$ with $F(\Gamma(g, y)) = \Gamma'(F(g), F(y))$ for all $g$.
   - For each $g$, the two sides are continuous lifts of $y \mapsto F(y)$ through $s$: both have source $F(y)$.
   - Two continuous lifts through the local homeomorphism $s$ agree on an open set ⟦Chapter13/StrongBundlePullMap · EpGroupoid.isOpen_setOf_eq_of_src⟧.
   - $E$ is a finite intersection of such sets, so open. It contains $x$, since $\Gamma(g, x)$ is $g$ and $F$ maps it to $F(g)$.
4. Restrict $N_0$ to its invariant core in $E$ (§XIII.1). Properness passes to the closed subset.

The text arranges $F(U(x)) = U'(F(x))$ "without loss of generality". The inclusion with injectivity is all that is used.

**Adapted good systems** ⟦Chapter13/MultisectionPullback · SBLocalization.PullMap.PullData⟧ ⟦Chapter13/MultisectionPullback · SBLocalization.PullMap.exists_pullData⟧. For a good system $\mathcal U'$ of $X'$ and open sets $V(x)$, there is a good system of $X$ with $U(x) \subset V(x)$ and each $N(x)$ adapted to $N'(F(x))$.
- Properness is from the existence lemma.
- Condition (3) is the text's argument ⟦Chapter13/MultisectionPullback · SBLocalization.PullMap.isDiffeoComponent_of_isPull⟧.
  1. $F$ maps $\mathcal U(x, x')$ into $\mathcal U'(F(x), F(x'))$ ⟦Chapter13/MultisectionPullback · SBLocalization.PullMap.mem_morBetween⟧, and maps components into components ⟦Chapter13/MultisectionPullback · SBLocalization.PullMap.mapsTo_connectedComponentIn⟧, by continuity.
  2. Let $\psi_1, \psi_2$ in a component $\Sigma$ have the same source. Their images lie in one component of $\mathcal U'$, where $s$ is injective, so $F(\psi_1) = F(\psi_2)$.
  3. Then $F(t\psi_1) = F(t\psi_2)$, so $t\psi_1 = t\psi_2$ by injectivity of $F$ on $U(x')$.
  4. Faithfulness gives $\psi_1 = \psi_2$. The same for $t$.
- No paracompactness is used: the system is built point by point, and the good-system conditions are checked directly.

*$F$ intertwines the bi-actions* ⟦Chapter13/MultisectionPullback · SBLocalization.PullMap.IsPullNbhd.mor_biact⟧: $F(g' * \varphi * g) = F(g') * F(\varphi) * F(g)$, from the identity for $\Gamma$ and functoriality.

**The pulled-back structure.** Let $(\Lambda', \mathcal U', S', \tau')$ be a structured tuple and take an adapted good system.
- *Index sets* $I_x = I'_{F(x)}$, with $G_x$ acting through $F : G_x \to G'_{F(x)}$.
- *Sections* $\text{pull}\ s'^{F(x)}_i$ on $U(x)$. The symmetric structure is ⟦Chapter13/MultisectionPullback · SBLocalization.PullMap.pullStructure⟧, and the decoration ⟦Chapter13/MultisectionPullback · SBLocalization.PullMap.pullDecoration⟧.
  - Equivariance: apply $\Phi^{-1}$ to the equivariance of $s'$ at $F(g)$, with $F(g * z) = F(g) * F(z)$ and $\Phi\mu = \mu'\Phi$.
  - Count: the count of $s'$ at $\Phi(w)$.
- *Correspondences* $\tau_{x,y}(\varphi) = \tau'_{F(x),F(y)}(F(\varphi))$ ⟦Chapter13/MultisectionPullback · SBLocalization.PullMap.pullTau⟧.
  - Local constancy and finiteness come from those of $\tau'$, through the continuity of $F$ and the inclusion $F(\mathcal U(x, y)) \subset \mathcal U'(F(x), F(y))$.
  - Equivariance: the bi-action on correspondences for actions through a homomorphism is the bi-action of the images ⟦Chapter13/MultisectionPullback · SBLocalization.PullMap.biact_compHom⟧. With the intertwining of the bi-actions on morphisms, it is that of $\tau'$.
  - The diagonal $[\mathrm{id}, g]$ for the action through $F$ is $[\mathrm{id}, F(g)]$ ⟦Chapter13/MultisectionPullback · SBLocalization.PullMap.ofPerm_compHom⟧.
  - Compatibility: $\Phi^{-1}$ applied to that of $\tau'$, since $F$ maps components into components.
- The structured tuple is ⟦Chapter13/MultisectionPullback · SBLocalization.PullMap.pullTuple⟧, so $\Phi^*\Lambda'$ is structurable ⟦Chapter13/MultisectionPullback · SBLocalization.PullMap.isStructurable_pull⟧.

**Canonicity** ⟦Chapter13/MultisectionPullback · SBLocalization.PullMap.pullTuple_equiv⟧. Equivalent structured tuples, pulled back over any two adapted good systems, give equivalent tuples.
1. Take an adapted good system inside both pulled-back systems and adapted to the common system of the two given tuples.
2. On it the index sets are equal, $I'_{F(x)}$ for both, and the correspondences agree because the given ones agree on the common system and $F$ maps into it.

So the pull-back is a map of structured classes ⟦Chapter13/MultisectionPullback · SBLocalization.PullMap.pullStructured⟧ ⟦Chapter13/MultisectionPullback · SBLocalization.PullMap.pullStructured_mk⟧, over the pull-back of functors ⟦Chapter13/MultisectionPullback · SBLocalization.PullMap.forget_pullStructured⟧.

**Theorem 13.4.1** (stronger), pp. 621–622 ⟦Chapter13/MultisectionPullback · SBLocalization.theorem_13_4_1⟧ ⟦Chapter13/MultisectionPullback · SBLocalization.theorem_13_4_1_structured⟧. For a strong bundle equivalence $\Phi$ over the equivalence $F$:
- $\Phi^*\Lambda'$ is structurable when $\Lambda'$ is;
- there is a map of structured classes over $\Phi^*$, given on every representative and every adapted good system by the pulled-back structure:
$$I_x = I'_{F(x)}, \qquad \Phi(s^x_i(z)) = s'^{F(x)}_i(F(z)), \qquad \tau_{x,y}(\varphi) = \tau'_{F(x),F(y)}(F(\varphi)).$$

*Stronger*: the text's "canonical way" is read as this map. Its independence of all choices is asserted in the text and proved here. No hypothesis is added; paracompactness is not used.

### XIII.20 Charts along a morphism: the tool of Proposition 13.4.2 and Theorem 13.4.3

Proposition 13.4.2 and Theorem 13.4.3 both move a structure from a point to an isomorphic point. The text does it in two ways: through $F|_{U(x_y)}$ for points in $F(X)$, and through $t \circ (s|_{U(\psi)})^{-1}$ for points reached by a morphism $\psi$. The formalization does both moves at once, by one chart along a morphism. This subsection sets the chart up, for a strong bundle equivalence $\Phi$ over $F : X \to X'$. Proposition 13.4.2 uses it for $F$ the identity.

**The chart at $y \in X'$** ⟦Chapter13/SymmetricStructurePush · SBLocalization.PushChart⟧.
- *Choices.* $F$ is essentially surjective, so there are $x_y \in X$ and a morphism $\sigma_y : F(x_y) \to y$.
- *The transport chart* (Chapter 10, Part X) is
$$Q = t \circ (s|_{\text{sheet of }\sigma_y})^{-1} \circ F$$
  near $x_y$. It comes with morphisms $\psi_u : F(u) \to Q(u)$, $\psi_u$ the morphism of the sheet through $\sigma_y$ with source $F(u)$. $Q$ is an sc-diffeomorphism from an open $W \ni x_y$ onto an open $W' \ni y$, with inverse $Q^{-1}$.
- A chart is chosen at every $y$ ⟦Chapter13/SymmetricStructurePush · SBLocalization.pushChart⟧.
- For $y = F(x)$ and $\sigma_y$ the unit, $Q$ is the text's $F|_{U(x_y)}$.

**The isotropy isomorphism** ⟦Chapter13/SymmetricStructurePush · SBLocalization.conjEquiv⟧. $g \mapsto \psi \circ F(g) \circ \psi^{-1}$, $G_{x_y} \to G'_y$, with $\psi = \psi_{x_y}$, is a group isomorphism (Remark 10.1.12, Part X). It is bijective because $F$ is an equivalence.

**Push neighbourhoods** ⟦Chapter13/SymmetricStructurePush · SBLocalization.IsPushNbhd⟧. For a neighbourhood $N$ of $x_y$ with the natural action, a neighbourhood $N'$ of $y$ with the natural action is a push neighbourhood if:
- $U' \subset W'$ and $Q^{-1}(U') \subset U$;
- $Q^{-1}(U')$ is invariant under $G_{x_y}$ within the chart;
- the natural actions are intertwined (2021 (10.2)–(10.3)): for $u = Q^{-1}(z)$,
$$\Gamma'(\psi F(g)\psi^{-1}, z) = \psi_{g * u} \circ F(\Gamma(g, u)) \circ \psi_u^{-1}.$$

Consequences:
- $(\psi F(g)\psi^{-1}) * z = Q(g * Q^{-1}(z))$ ⟦Chapter13/SymmetricStructurePush · SBLocalization.IsPushNbhd.Φ_eq⟧, applying $t$.
- The identity $\Gamma'(\cdot, z) \circ \psi_u = \psi_{g*u} \circ F(\Gamma(g, u))$ ⟦Chapter13/SymmetricStructurePush · SBLocalization.IsPushNbhd.Γ_comp_ψ⟧.

*Existence, with the properness property* ⟦Chapter13/SymmetricStructurePush · SBLocalization.exists_isPushNbhd⟧.
1. Inside $Q(W_0)$, with $W_0$ the invariant core of $U$ in the chart domain, take a neighbourhood of $y$ with the natural action and proper closure (§XIII.1).
2. The two lifts $z \mapsto \Gamma'(\psi F(g)\psi^{-1}, z)$ and $z \mapsto \psi_{g*u} \circ F(\Gamma(g, u)) \circ \psi_u^{-1}$ through $s$ are continuous, have source $z$, and agree at $y$. So they agree on an open set, as in §XIII.19.
3. Restrict to the invariant core of that open set.

**Pushed sections** ⟦Chapter13/SymmetricStructurePush · SBLocalization.pushSec⟧: $z \mapsto \mu'(\psi_u, \Phi(s(u)))$ with $u = Q^{-1}(z)$, the transported section of §XIII.9 along $\psi \circ Q^{-1}$. For an sc⁺-section $s$ on $U$ it is an sc⁺-section on $U'$ ⟦Chapter13/SymmetricStructurePush · SBLocalization.IsPushNbhd.isScPlusSectionOn_pushSec⟧:
- $Q^{-1}$ is sc-smooth;
- $\Phi$ is a strong bundle map;
- $z \mapsto \psi_{Q^{-1}(z)}$ is sc-smooth, a composite of the sheet inverse with $F$.

**The pushed symmetric structure** ⟦Chapter13/SymmetricStructurePush · SBLocalization.pushStructure⟧. A symmetric structure of $\Lambda$ on $N$ gives one of $\Phi_*\Lambda$ on $N'$:
- $I'_y = I_{x_y}$, with $G'_y$ acting through the inverse of the isotropy isomorphism;
- $s'_i = \text{push}\ s_i$.

Equivariance is the intertwining identity together with $\Phi\mu = \mu'\Phi$ and the composition law of $\mu'$. The count: $\text{push}\ s_i(z) = w'$ iff $s_i(u) = \Phi^{-1}(\mu'(\psi_u^{-1}, w'))$. $\Phi_*\Lambda$ at $w'$ is $\Lambda$ at that vector, Chapter 11's push-forward being defined through any preimage.

**Lifting morphisms** ⟦Chapter13/MultisectionPushforward · SBLocalization.PushChart.liftMor⟧. For charts $T$ at $y$ and $T'$ at $y'$ and a morphism $\varphi'$ from $W'$ to $W'_{T'}$, the lift is the unique $\varphi : u \to u'$, $u = Q^{-1}(s\varphi')$, $u' = Q'^{-1}(t\varphi')$, with
$$\psi'_{u'} \circ F(\varphi) = \varphi' \circ \psi_u$$
⟦Chapter13/MultisectionPushforward · SBLocalization.PushChart.comp_liftMor⟧.
- *Existence:* $F$ is full, so the morphism $\psi'^{-1}_{u'} \circ \varphi' \circ \psi_u : F(u) \to F(u')$ is $F(\varphi)$ for some $\varphi$.
- *Uniqueness:* $F$ is faithful.

Properties of the lift:
- *Continuous* ⟦Chapter13/MultisectionPushforward · SBLocalization.PushChart.continuousOn_liftMor⟧. A map into the morphisms of $X$ is continuous at a point when its source, target and $F$-image are ⟦Chapter13/MultisectionPushforward · SBLocalization.PushChart.continuousAt_of_mor⟧. $F$ on morphisms is a local sc-diffeomorphism, so near $f(a)$ a local inverse recovers $f$ from $F \circ f$, provided $f$ stays in the sheet. That is forced by faithfulness, and by the continuity of $s \circ f$ and $t \circ f$, which pin the sheet. For the lift, source and target are $Q^{-1}$ and $Q'^{-1}$ of continuous functions, and the $F$-image is $\psi' \circ \varphi' \circ \psi^{-1}$, continuous.
- *Injective* ⟦Chapter13/MultisectionPushforward · SBLocalization.PushChart.injOn_liftMor⟧: $\varphi'$ is recovered as $\psi' \circ F(\varphi) \circ \psi^{-1}$.
- *Functorial* ⟦Chapter13/MultisectionPushforward · SBLocalization.PushChart.liftMor_comp⟧ ⟦Chapter13/MultisectionPushforward · SBLocalization.PushChart.liftMor_inv⟧: by uniqueness of lifts.
- *Compatible with $\Gamma$* ⟦Chapter13/MultisectionPushforward · SBLocalization.PushChart.liftMor_Γ⟧: the lift of $\Gamma'(\psi F(g)\psi^{-1}, z)$ is $\Gamma(g, Q^{-1}z)$, by the intertwining identity.
- *Compatible with the bi-action* ⟦Chapter13/MultisectionPushforward · SBLocalization.PushChart.liftMor_biact⟧: from functoriality and compatibility with $\Gamma$.
- *Carries components to components* ⟦Chapter13/MultisectionPushforward · SBLocalization.PushChart.isDiffeoComponent_push⟧. A component $\Sigma'$ of $\mathcal U'(y, y')$ is mapped by the continuous lift into a component $\Sigma$ of $\mathcal U(x_y, x_{y'})$, where $s$ and $t$ are injective. The lift is injective, and source and target of the lift determine those of $\varphi'$ through $Q$, $Q'$. So condition (3) of good systems is carried forward.
- *The pushed sections are compatible along the lift* ⟦Chapter13/MultisectionPushforward · SBLocalization.PushChart.pushSec_compat⟧: $\mu'(\varphi', \text{push}\ s(s\varphi')) = \mu'(\psi'_{u'}, \Phi(\mu(\varphi, s(u))))$, by $\varphi' \circ \psi_u = \psi'_{u'} \circ F(\varphi)$ and $\Phi\mu = \mu'\Phi$.

### XIII.21 Proposition 13.4.2 (2017: Proposition 13.6): extension from an open $V$ with $|V| = |X|$

**Structured data on $V$.** The text takes the strong bundle $W|V$ over the open full sub-ep-groupoid $V$ and a structured sc⁺-multisection functor on it. The project has no strong bundle over an open sub-ep-groupoid, so the data are read relative to $V$ inside $W$.
- *A functor on $W|V$* ⟦Chapter13/StructuredExtensionData · SBLocalization.IsWFunctorOn⟧ is a $\Lambda : W \to \mathbb Q^+$ invariant along morphisms with both ends in $V$. Its values over $X \setminus V$ are irrelevant. Two vectors over $V$ in one orbit have the same value ⟦Chapter13/StructuredExtensionData · SBLocalization.IsWFunctorOn.eq_of_π_eq⟧, since the morphism joining them has both ends in $V$.
- *An sc⁺-multisection on $W|V$* ⟦Chapter13/StructuredExtensionData · SBLocalization.IsScPlusMultisectionOn⟧ is such a functor with a local section structure around every $q \in V$ on the domain of a natural representation inside $V$. The natural representations of the ep-groupoid $V$ are those of $X$ with domain in $V$.
- *Structured data on $V$* ⟦Chapter13/StructuredExtensionData · SBLocalization.StructuredOn⟧ are Definitions 13.3.4 and 13.3.6 with every index in $V$:
  - neighbourhoods $N(q)$, $q \in V$, with $U(q) \subset V$, good for $V$ in the sense of Theorem 13.1.7 as printed (§XIII.5);
  - symmetric structures $(I_q, s^q_i)$ representing $\Lambda$ on $U(q)$;
  - correspondences $\tau_{q,q'}$ on $\mathcal U(q, q')$, locally constant with finitely many values, with the bi-action, the compatibility with the sections, the diagonal and the swap.

  Each $I_q$ is nonempty, by the argument of §XIII.9.
- *Witness.* Every structured tuple on $X$ gives structured data with $V = X$ ⟦Chapter13/StructuredExtensionData · SBLocalization.StructuredTuple.toStructuredOn⟧, for instance the zero multisection's on a paracompact orbit space.

**The extension functor** ⟦Chapter13/StructuredExtensionData · SBLocalization.extendMult⟧. $\bar\Lambda(w) = \Lambda(w_0)$ for some $w_0$ over $V$ in the orbit of $w$ in $W$.
- Such $w_0$ exists because $\pi(V) = |X|$ ⟦Chapter13/StructuredExtensionData · SBLocalization.exists_mem_of_π_image⟧. A morphism $\varphi : q \to P(w)$ with $q \in V$ gives $w_0 = \mu(\varphi^{-1}, w)$.
- The value does not depend on the choice, by the previous paragraph, and depends only on the orbit of $w$ ⟦Chapter13/StructuredExtensionData · SBLocalization.extendMult_congr⟧.
- It is a functor on $W$ ⟦Chapter13/StructuredExtensionData · SBLocalization.isWFunctor_extendMult⟧, because $w$ and $\mu(\varphi, w)$ have the same orbit.
- It equals $\Lambda$ over $V$ ⟦Chapter13/StructuredExtensionData · SBLocalization.extendMult_eq⟧: for $w$ over $V$, take $w_0 = w$.
- Every functor on $W$ that agrees with $\Lambda$ over $V$ is $\bar\Lambda$ ⟦Chapter13/StructuredExtensionData · SBLocalization.eq_extendMult⟧, since every orbit meets $V$.

This uniqueness is how "canonical" is read.

**Unit charts.** At a point $q \in V$ the extension keeps the given data, through the *unit chart* of the identity equivalence ⟦Chapter13/StructuredExtensionData · SBLocalization.unitChart⟧: $Q = \mathrm{id}$ and $\psi_u = 1_u$.
- The identity is a strong bundle equivalence ⟦Chapter13/StructuredExtensionData · SBLocalization.equivalences_id_sep⟧, and push-forward along it is the identity on functors ⟦Chapter13/StructuredExtensionData · SBLocalization.pushMult_id⟧.
- A neighbourhood is a push neighbourhood of itself for the unit chart ⟦Chapter13/StructuredExtensionData · SBLocalization.isPushNbhd_unit⟧, because the isotropy isomorphism is the identity.
- Pushed sections are the given sections ⟦Chapter13/StructuredExtensionData · SBLocalization.pushSec_unit⟧ and lifted morphisms are the given morphisms ⟦Chapter13/StructuredExtensionData · SBLocalization.liftMor_unit⟧, since $\mu(1, w) = w$.
- Push neighbourhoods pass to smaller neighbourhoods with the same action ⟦Chapter13/StructuredExtensionData · SBLocalization.IsPushNbhd.of_le⟧.

**Extension charts** ⟦Chapter13/StructuredExtensionData · SBLocalization.ExtChart⟧. At a point $x$, an extension chart consists of:
- a point $q_x \in V$ and a morphism $\psi_x : q_x \to x$;
- the transport chart of the identity along $\psi_x$, $Q = t \circ (s|_{\text{sheet of }\psi_x})^{-1}$, which is the text's $D_x$;
- a push neighbourhood $U(x)$ of $U(q_x)$ with the properness property.

Charts are chosen as follows.
- At $x \in V$ the unit chart is used ⟦Chapter13/StructuredExtensionData · SBLocalization.unitExt⟧.
- At $x \notin V$ a chart exists inside any open $O \ni x$ ⟦Chapter13/StructuredExtensionData · SBLocalization.exists_extChart⟧: §XIII.20 with $F = \mathrm{id}$, then restriction to $O$.
- A choice of all charts with these properties ⟦Chapter13/StructuredExtensionData · SBLocalization.ExtSetup⟧ ⟦Chapter13/StructuredExtensionData · SBLocalization.extChart⟧ gives unit charts on $V$ ⟦Chapter13/StructuredExtensionData · SBLocalization.extChart_of_mem⟧.

**The extended structure.**
1. *At each $x$* ⟦Chapter13/StructuredExtension · SBLocalization.ExtChart.sym⟧: the structure at $q_x$ pushed along the chart, $I_x = I_{q_x}$. For the identity equivalence, $\Phi_*\bar\Lambda = \bar\Lambda$, and $\bar\Lambda = \Lambda$ over $U(q_x) \subset V$. So the pushed structure represents $\bar\Lambda$ on $U(x)$. Hence $\bar\Lambda$ is an sc⁺-multisection on $W$ ⟦Chapter13/StructuredExtension · SBLocalization.isScPlusMultisection_extendMult⟧: a symmetric structure gives a local section structure ⟦Chapter13/StructuredExtension · SBLocalization.hasLocalSectionStructure_of_symmetricOn⟧.
2. *Correspondences* ⟦Chapter13/StructuredExtension · SBLocalization.ExtChart.tau⟧: $\tau_{x,x'}(\varphi) = \tau_{q_x,q_{x'}}(\text{lift}\,\varphi)$, with the lift of §XIII.20 through the two charts.
   - The text distinguishes three cases: both ends in $V$, one end, neither, with maps $A$ and $C$ and a pseudo-inverse. The lift covers them uniformly. For the identity, the lift is the text's $C$; it is $A$ when $x \in V$ and its inverse when $x' \in V$.
3. *The good system* ⟦Chapter13/StructuredExtension · SBLocalization.extGood⟧ of the chart neighbourhoods. Condition (3) is carried from $(U(q))_{q \in V}$ by the lift ⟦Chapter13/StructuredExtension · SBLocalization.ExtChart.isDiffeoComponent⟧, as in §XIII.20.
4. *The decoration, the structure and the tuple* ⟦Chapter13/StructuredExtension · SBLocalization.extDecoration⟧ ⟦Chapter13/StructuredExtension · SBLocalization.extTau⟧ ⟦Chapter13/StructuredExtension · SBLocalization.extTuple⟧. The conditions of Definitions 13.3.4 and 13.3.6 for $\tau$ are those of the given $\tau_{q,q'}$, through the properties of the lift: continuity, functoriality, compatibility with $\Gamma$ and the bi-action, and compatibility of pushed sections.
5. *The given data are kept at the points of $V$.* There the charts are unit charts, so:
   - the actions on the index sets are the given ones ⟦Chapter13/StructuredExtension · SBLocalization.extSym_smul_of_eq⟧;
   - the sections are the given ones ⟦Chapter13/StructuredExtension · SBLocalization.extSym_s_of_eq⟧;
   - the correspondences on $\mathcal U(q, q')$ are the given ones ⟦Chapter13/StructuredExtension · SBLocalization.extTau_of_eq⟧.

   All three hold through the identifications of the index types.

**Proposition 13.4.2** (restated), pp. 623–625 ⟦Chapter13/StructuredExtension · SBLocalization.proposition_13_4_2⟧. Let $V$ be open with $\pi(V) = |X|$, and structured data on $V$ for $\Lambda$ be given.
- (1) $\bar\Lambda$ is an sc⁺-multisection on $W$, equal to $\Lambda$ over $V$, and the only functor on $W$ with this property.
- (2) For every family of open $O(x) \ni x$ there is a structured tuple for $\bar\Lambda$ with the following properties:
  - its neighbourhoods at $q \in V$ are the given $U(q)$, and $U(x) \subset O(x)$ for $x \notin V$;
  - its index sets with their $G_q$-actions, its sections on $U(q)$ and its correspondences on $\mathcal U(q, q')$ are the given ones at the points of $V$.

*Structurable* ⟦Chapter13/StructuredExtension · SBLocalization.proposition_13_4_2_structurable⟧: $\bar\Lambda$ is structurable.

*Restated*: the structured data relative to $V$ replace a structure on the bundle $W|V$. The good-system condition on $V$ is that of Theorem 13.1.7 as printed for the open $V$. "Canonical" is uniqueness among functors. No hypothesis is added.

### XIII.22 Theorem 13.4.3 (2017: Theorem 13.4): push-forward along a strong bundle equivalence, and generalized strong bundle isomorphisms

**The pushed good system** ⟦Chapter13/MultisectionPushforward · SBLocalization.pushGood⟧. Let $\Phi$ be a strong bundle equivalence over $F : X \to X'$ and $(\Lambda, \mathcal U, S, \tau)$ a structured tuple.
- At each $y \in X'$, take the chart of §XIII.20 and a push neighbourhood of $U(x_y)$ ⟦Chapter13/MultisectionPushforward · SBLocalization.pushNbhd⟧ ⟦Chapter13/MultisectionPushforward · SBLocalization.isPushNbhd_pushNbhd⟧.
- Properness holds by construction.
- Condition (3) holds by the lift.

**The pushed structure.**
- *Decoration* ⟦Chapter13/MultisectionPushforward · SBLocalization.pushDecoration⟧: the pushed symmetric structures of §XIII.20, $I'_y = I_{x_y}$.
- *Correspondences* ⟦Chapter13/MultisectionPushforward · SBLocalization.pushTau⟧: $\tau'_{y,y'}(\varphi') = \tau_{x_y,x_{y'}}(\text{lift}\,\varphi')$.
  - Local constancy: $\tau$ is locally constant and the lift continuous.
  - Finiteness: values of $\tau$.
  - Equivariance: compatibility of the lift with the bi-action, and the isotropy isomorphisms on index sets.
  - Diagonal: the lift of $\Gamma'$ is $\Gamma$.
  - Swap: the lift of an inverse is the inverse of the lift.
  - Compatibility: the pushed sections are compatible along the lift, and the lift maps components into components.
- *The tuple* ⟦Chapter13/MultisectionPushforward · SBLocalization.pushTuple⟧.

**Theorem 13.4.3** (same), pp. 625–626 ⟦Chapter13/MultisectionPushforward · SBLocalization.theorem_13_4_3⟧ ⟦Chapter13/MultisectionPushforward · SBLocalization.theorem_13_4_3_structured⟧. $\Phi_*\Lambda$, Chapter 11's push-forward, is structurable when $\Lambda$ is. A structured tuple pushes to a structured tuple with $I'_y = I_{x_y}$ and the pushed sections and correspondences.

*Where the formal proof departs from the text.* The text structures $\Phi_*\Lambda$ on $F(X)$ through $F|_{U(x_y)}$, then extends by Proposition 13.4.2 from $F(X)$, which has $|F(X)| = |X'|$. The formal proof gives every $y$, in $F(X)$ or not, a chart along $\sigma_y$. This does both steps at once and does not use Proposition 13.4.2. No canonicity is claimed, as in the text. No hypothesis is added.

**Generalized strong bundle isomorphisms.** A diagram $W \xleftarrow{\Phi} V \xrightarrow{\Psi} W'$ of strong bundle equivalences gives push-forwards $[D]_* = \Psi_*\Phi^*$ and pull-backs $[D]^* = \Phi_*\Psi^*$ of functors (Chapter 11, Part XI). Composing Theorems 13.4.1 and 13.4.3:
- both preserve structurability ⟦Chapter13/MultisectionPushforward · SBLocalization.SDiagram.isStructurable_pushMult⟧ ⟦Chapter13/MultisectionPushforward · SBLocalization.SDiagram.isStructurable_pullMult⟧;
- so do push-forwards and pull-backs along a generalized strong bundle isomorphism ⟦Chapter13/MultisectionPushforward · SBLocalization.GenSBMap.isStructurable_pushMult⟧ ⟦Chapter13/MultisectionPushforward · SBLocalization.GenSBMap.isStructurable_pullMult⟧, through any representing diagram.

The text says this "follows immediately" at the opening of §16.5. The interior case of Proposition 14.1.8 uses it (Part XIV).

### XIII.23 Theorem 13.4.4 (2017: Theorem 13.5): pull-back along a proper strong bundle covering

**Theorem 13.4.4** (same), pp. 626–628 ⟦Chapter13/MultisectionPullback · SBLocalization.theorem_13_4_4⟧ ⟦Chapter13/MultisectionPullback · SBLocalization.theorem_13_4_4_structured⟧. For a proper strong bundle covering $\Phi : W \to W'$ over $F : X \to X'$, the 2021 Definition 8.5.9 (Part VIII):
- $\Phi^*\Lambda'$ is structurable when $\Lambda'$ is;
- a structured $\Lambda'$ gives a structured class on $\Phi^*\Lambda'$, with $I_y = I'_{F(y)}$, $G_y$ acting through $F$, $\Phi(s^y_i(z)) = s'^{F(y)}_i(F(z))$, and $\tau_{y,y'}(\varphi) = \tau'_{F(y),F(y')}(F(\varphi))$;
- the same canonicity as Theorem 13.4.1 holds.

*Proof.* The covering gives pull-back data (§XIII.19) ⟦Chapter13/StrongBundlePullMap · SBLocalization.PullMap.ofCovering⟧.
1. $\Phi$ intertwines the actions and is a local strong bundle isomorphism: Definition 8.5.9.
2. $F$ is faithful: by Definition 8.5.1 (3) the map $\varphi \mapsto (F(\varphi), s(\varphi))$ is an sc-diffeomorphism onto the fibred product, so two morphisms with the same source and the same image agree.
3. The rest is the construction of §XIII.19, word for word.
   - The text's identity $F(\Gamma_Y(g, z)) = \Gamma_X(F(g), F(z))$ is the third clause of an adapted neighbourhood. It is obtained by the same open-set argument.
   - The text's disjoint decomposition $F^{-1}(U(x)) = \bigsqcup V(z)$ is not needed: adapted neighbourhoods suffice, since only injectivity of $F$ on $U(y)$ and $F(U(y)) \subset U'(F(y))$ enter.

No hypothesis is added; paracompactness is not used.

### XIII.24 Definition 13.4.5 (2017: Definition 13.22): commensurable structured sc⁺-multisections and their sums

**A choice of common data** ⟦Chapter13/Commensurable · SBLocalization.CommData⟧. A choice $c$ consists of:
- a good system $\mathcal U$;
- nonempty finite index types $I_x$ with $G_x$-actions;
- maps $\tau_{x,x'}$ from morphisms to $J(I_x, I_{x'})$ satisfying the conditions of Definitions 13.3.4 (1)–(2) and 13.3.6 (1)–(2), which do not involve sections.

The actions are determined by $\tau$ ⟦Chapter13/Commensurable · SBLocalization.CommData.smul_eq_of_diag⟧. By Definition 13.3.6 (1) at $y = x$, $\tau_{x,x}(\Gamma(g, x)) = [\mathrm{id}, g]$, and $[\mathrm{id}, e] = [\mathrm{id}, e']$ only if $e = e'$ ⟦Chapter13/Commensurable · SBLocalization.IndexCorr.ofEquiv_injective⟧: an equivalence $c$ of the two diagrams satisfies $c = \mathrm{id}$, from the first leg, and then $e = e'$. So including the actions in $c$ adds nothing to the text's "$\tau_1 = \tau_2$".

**Sections over $c$** ⟦Chapter13/Commensurable · SBLocalization.CommData.Sections⟧ are sections $s^x_i$, $i \in I_x$, on every $U(x)$ that are:
- sc⁺;
- equivariant;
- compatible with $\tau$ in the sense of Definition 13.3.4 (3) ⟦Chapter13/Commensurable · SBLocalization.CommData.Compat⟧.

No functor is given yet; the counting formula defines one:
- $\mathrm{count}_x(w) = |I_x|^{-1}\#\{i : s^x_i(P(w)) = w\}$ ⟦Chapter13/Commensurable · SBLocalization.CommData.countAt⟧;
- the functor takes the count at $x = P(w)$ ⟦Chapter13/Commensurable · SBLocalization.CommData.sumMult⟧.

*Data over $c$ for a given $\Lambda$* ⟦Chapter13/Commensurable · SBLocalization.CommData.Over⟧ are sections over $c$ with the counting formula for $\Lambda$ on every $U(x)$. They give a structured tuple and a structured class ⟦Chapter13/Commensurable · SBLocalization.CommData.Over.toStructured⟧. Every structured tuple $T$ is of this form, over its own choice ⟦Chapter13/Commensurable · SBLocalization.CommData.ofTuple⟧ ⟦Chapter13/Commensurable · SBLocalization.CommData.Over.ofTuple_toTuple⟧. The index sets are nonempty there because the index sets of every symmetric structure are (§XIII.9).

**Count transport along a correspondence** ⟦Chapter13/Commensurable · SBLocalization.IndexCorr.count_eq_of_sat⟧. Let $I_x \xleftarrow{a} I \xrightarrow{b} I_{x'}$ represent $\tau$, with $s'_{b(k)} = f(s_{a(k)})$ for all $k$ and $f$ injective on the relevant values. Then
$$|I_x|^{-1}\#\{i : s_i = v\} = |I_{x'}|^{-1}\#\{j : s'_j = f(v)\}.$$
1. If $I_x$ is empty, so are $I$ and $I_{x'}$, by surjectivity, and both sides are $0$.
2. Let $p$ be the common fibre size of $a$ and $q$ that of $b$, both positive. Then $|I| = p|I_x| = q|I_{x'}|$ ⟦Chapter13/Commensurable · SBLocalization.IndexCorr.card_filter_comp_eq⟧, by counting $I$ fibrewise.
3. Count the $k \in I$ with $s_{a(k)} = v$ in two ways.
   - Fibrewise over $a$: $p\#\{i : s_i = v\}$.
   - The condition is equivalent to $s'_{b(k)} = f(v)$, by the relation and injectivity of $f$. Fibrewise over $b$: $q\#\{j : s'_j = f(v)\}$.
4. Divide by the equal numbers $p|I_x| = q|I_{x'}|$.

This is why the counting formula of (2) defines a functor and does not depend on $x$:
- *Along a morphism* ⟦Chapter13/Commensurable · SBLocalization.CommData.Sections.countAt_fibAct⟧: for $\varphi \in \mathcal U(x, x')$, $\mathrm{count}_x(v) = \mathrm{count}_{x'}(\mu(\varphi, v))$. Use compatibility at $\varphi$ itself and injectivity of $\mu(\varphi, \cdot)$.
- *Independent of $x$* ⟦Chapter13/Commensurable · SBLocalization.CommData.Sections.countAt_eq⟧: $\mathrm{count}_x(w) = \mathrm{count}_{P(w)}(w)$ for $P(w) \in U(x)$. Apply the previous item to the unit $1_{P(w)} \in \mathcal U(x, P(w))$.
- *A functor* ⟦Chapter13/Commensurable · SBLocalization.CommData.Sections.isWFunctor_sumMult⟧: apply the first item to $\varphi \in \mathcal U(s\varphi, t\varphi)$.
- *An sc⁺-multisection* ⟦Chapter13/Commensurable · SBLocalization.CommData.Sections.isScPlusMultisection_sumMult⟧: on each $U(x)$ the sections $s^x_i$ with weights $|I_x|^{-1}$ are a local structure, by independence of $x$.

**Definition 13.4.5 (1)** (restated), p. 628 ⟦Chapter13/Commensurable · SBLocalization.Commensurable⟧. Two structured classes are commensurable if they have representatives over one common $c$. The relation is reflexive ⟦Chapter13/Commensurable · SBLocalization.Commensurable.refl⟧, by the choice of the tuple itself, and symmetric ⟦Chapter13/Commensurable · SBLocalization.Commensurable.symm⟧. The paracompactness of $|X|$ in the text's setting is not needed for the definition. *Restated*: "representatives can be taken with $\mathcal U_1 = \mathcal U_2$, $\tau_1 = \tau_2$, $I^1_x = I^2_x$" is "data over one $c$".

**The locally finite commensurable sum** (same), p. 629 ⟦Chapter13/Commensurable · SBLocalization.CommData.definition_13_4_5_lf⟧. Let $(\Lambda_j)_{j \in J}$ be locally finite (Definition 13.2.12) with data over one $c$. Then:
- the sections $s^x_i = \sum_js^{j,x}_i$ are defined;
- they are sections over $c$;
- $\bigoplus^c_j\Lambda_j$, their count, is an sc⁺-multisection with these data, and $\Lambda(w) = |I_x|^{-1}\#\{i : s^x_i(P(w)) = w\}$ for $P(w) \in U(x)$.

*Proof.*
1. *Finitely many nonzero summands near each point* ⟦Chapter13/Commensurable · SBLocalization.CommData.exists_finite_support⟧. Over $O(y)$ of Definition 13.2.12, every $j$ outside the finite set has $\Lambda_j$ trivial, and its sections vanish there (§XIII.9).
2. So near each point $\sum_js^{j,x}_i$ is a finite sum of sections extended by zero ⟦Chapter13/Commensurable · SBLocalization.CommData.sumSec_eq_sectionSum⟧. Being sc⁺ on an open set is local ⟦Chapter13/Commensurable · SBLocalization.IsScPlusSectionOn.of_locally⟧, so the sum is sc⁺.
3. Equivariance and compatibility are additivity of $\mu(\psi, \cdot)$ over finitely supported sums ⟦Chapter13/Commensurable · SBLocalization.fibAct_finsum⟧. Compatibility of the sum needs one representative that works for all $j$ at once: the conjunction of the relations is saturated when each is ⟦Chapter13/Commensurable · SBLocalization.IndexCorr.sat_iInter⟧, since all $j$ share the same $\tau$.
4. The sections over $c$ are ⟦Chapter13/Commensurable · SBLocalization.CommData.lfSections⟧, and the count is an sc⁺-multisection by the previous paragraph.

"Pairwise commensurable" is read as "over one common $c$", which is what the text's notation $[\Lambda_j, \mathcal U, S_j, \tau]$ writes. "Locally finite" is Definition 13.2.12; the text's condition after Definition 13.4.5 is the same with "open". The text calls the construction evident; its well-definedness is the count transport above.

**Definition 13.4.5 (2)** (same), p. 628 ⟦Chapter13/Commensurable · SBLocalization.CommData.definition_13_4_5⟧. Over a common $c$, the sum $\Lambda_1 \oplus_c \Lambda_2$ has sections $s^x_i = s^{1,x}_i + s^{2,x}_i$, and $\Lambda(w) = |I_x|^{-1}\#\{i : s^x_i(P(w)) = w\}$ on $U(x)$. It is an sc⁺-multisection with these data. It is the locally finite sum over a two-element index set ⟦Chapter13/Commensurable · SBLocalization.CommData.commSum₂⟧. A finite family is locally finite, with $O(x) = X$.

The index set of $\Lambda_1 \oplus_c \Lambda_2$ is $I_x$, not $I^1_x \times I^2_x$. The commensurable sum is a different operation from the sum of §XIII.11. In general the two functors differ, since the commensurable sum adds sections with the same index only.

### XIII.25 Definition 13.5.1 (2017: Definition 13.23) and Remark 13.5.2 (2017: Remark 13.6): atomic sc⁺-multisections

**Atomic data** ⟦Chapter13/AtomicMultisection · SBLocalization.AtomicData⟧ are the data of Definition 13.5.1 (1)–(2), p. 629:
- a point $x$;
- a natural representation of $G_x$ on $U(x)$, with the properness property: $t : s^{-1}(\operatorname{cl}U(x)) \to X$ is proper;
- an open $V \ni x$, invariant under every $\Phi(g)$, with $\operatorname{cl}V \subset U(x)$;
- a finite index type $I$ with a $G_x$-action;
- sc⁺-sections $s_i$ on $U(x)$ that are equivariant, $s_{g(i)}(g * y) = \mu(\Gamma(g, y), s_i(y))$ for $y \in U(x)$, and vanish on $U(x) \setminus V$.

The text's "$G_x$-invariant open neighbourhood $U(x)$" is read here as the domain of a natural representation (Theorem 7.1.13, Part VII). A second reading, on neighbourhoods with the natural action, follows below. Both readings are used.

**The count, and condition (3).**
- *The count* ⟦Chapter13/AtomicMultisection · SBLocalization.AtomicData.count⟧ of a vector $w'$ is $|I|^{-1}\#\{i : s_i(P(w')) = w'\}$.
- *Reachable points* ⟦Chapter13/AtomicMultisection · SBLocalization.AtomicData.Reach⟧: $y$ is reachable if some morphism $\varphi$ has $s(\varphi) = y$ and $t(\varphi) \in U(x)$. The reachable points are the saturation of $U(x)$ ⟦Chapter13/AtomicMultisection · SBLocalization.AtomicData.reach_iff_mem_saturation⟧.
- *Condition (3)* ⟦Chapter13/AtomicMultisection · SBLocalization.AtomicData.IsRelated⟧. A functor $\Lambda$ is related to the data if two things hold:
  - $\Lambda(w)$ is the count of $\mu(\varphi, w)$ for every morphism $\varphi$ from $P(w)$ into $U(x)$;
  - $\Lambda$ agrees with the zero multisection over the points that are not reachable.
- *Atomic* (restated), p. 629 ⟦Chapter13/AtomicMultisection · SBLocalization.IsAtomic⟧: an sc⁺-multisection related to some atomic data.

**The count does not depend on the morphism.** The text writes condition (3) for any $\varphi$ with $t(\varphi) \in U(x)$, and does not say that the value is independent of the choice. It is.
1. *Equivariance permutes the indices* ⟦Chapter13/AtomicMultisection · SBLocalization.AtomicData.card_filter_μ_Γ⟧. For $g \in G_x$ and $y \in U(x)$, the permutation $i \mapsto g(i)$ is a bijection from $\{i : s_i(y) = w\}$ to $\{i : s_i(g * y) = \mu(\Gamma(g, y), w)\}$. This is the equivariance of the sections, together with injectivity of $\mu(\Gamma(g, y), \cdot)$ on the fibre.
2. *So the count is invariant under the $\Gamma(g, \cdot)$* ⟦Chapter13/AtomicMultisection · SBLocalization.AtomicData.count_μ_Γ⟧.
3. *Two morphisms from $P(w)$ into $U(x)$ give the same count* ⟦Chapter13/AtomicMultisection · SBLocalization.AtomicData.count_μ_eq⟧.
   - For $\varphi, \varphi'$ from $P(w)$ into $U(x)$, the morphism $\psi = \varphi' \circ \varphi^{-1}$ joins two points of $U(x)$. So it is $\Gamma(g, t\varphi)$ for some $g \in G_x$: the natural representation is onto the morphisms between points of $U(x)$.
   - Then $\mu(\varphi', w) = \mu(\psi, \mu(\varphi, w))$, and step 2 applies.

**The multisection of the data** ⟦Chapter13/AtomicMultisection · SBLocalization.AtomicData.mult⟧. It is the count of $\mu(\varphi, w)$ for some $\varphi$ from $P(w)$ into $U(x)$ when $P(w)$ is reachable, and the zero multisection otherwise.
- It is computed by any such $\varphi$ ⟦Chapter13/AtomicMultisection · SBLocalization.AtomicData.mult_eq⟧, by the previous paragraph.
- Off the reachable points it is trivial ⟦Chapter13/AtomicMultisection · SBLocalization.AtomicData.mult_of_not_reach⟧.
- Over $U(x)$ it is the count itself ⟦Chapter13/AtomicMultisection · SBLocalization.AtomicData.mult_of_mem⟧, by the unit morphism.
- It is related to the data ⟦Chapter13/AtomicMultisection · SBLocalization.AtomicData.isRelated_mult⟧.
- *Every functor related to the data is this one* ⟦Chapter13/AtomicMultisection · SBLocalization.AtomicData.IsRelated.eq_mult⟧. So an atomic $\Lambda$ is determined by its data.
- *It is a functor* ⟦Chapter13/AtomicMultisection · SBLocalization.AtomicData.isWFunctor_mult⟧. For a morphism $\psi$ and $w$ over $s(\psi)$: if $s(\psi)$ is reachable through $\varphi$, then $t(\psi)$ is reachable through $\varphi \circ \psi^{-1}$, and the two counts are those of the same vector. If not, neither is reachable, and the zero multisection is a functor.

**Condition (2) as printed** ⟦Chapter13/AtomicMultisection · SBLocalization.AtomicData.IsRelated.symmetricStructure⟧. For a $\Lambda$ related to the data, the data are a symmetric structure of $\Lambda$ on $U(x)$ in the sense of Definition 13.2.5 (§XIII.9). The representation on $U(x)$ is the count. So the reading of (2) as "sections with a $G_x$-action and equivariance" agrees with the text's "symmetric sc⁺-section structure".

**The index set is nonempty** ⟦Chapter13/AtomicMultisection · SBLocalization.AtomicData.IsRelated.nonempty⟧. For $\Lambda$ an sc⁺-multisection related to the data, $I \neq \emptyset$.
- The weights of $\Lambda$ over $x$ sum to $1$, so some vector over $x$ has positive weight.
- With $I = \emptyset$ the count of every vector is $0$.

The text does not say this. It matters for Theorem 13.5.5 (§XIII.28).

**The local structure of the multisection of the data.**
1. *Properness passes to $\operatorname{cl}V$* ⟦Chapter13/AtomicMultisection · SBLocalization.AtomicData.isProperSubset_closure_V⟧: a closed subset of the proper $\operatorname{cl}U(x)$.
2. *The saturation of $\operatorname{cl}V$ is closed* ⟦Chapter13/AtomicMultisection · SBLocalization.AtomicData.isClosed_saturation_closure_V⟧. This is the closedness of saturations of proper sets (Part VII). It lies in the saturation of $U(x)$ ⟦Chapter13/AtomicMultisection · SBLocalization.AtomicData.saturation_closure_V_subset⟧.
3. *Off the saturation of $\operatorname{cl}V$ the multisection is trivial* ⟦Chapter13/AtomicMultisection · SBLocalization.AtomicData.mult_eq_zeroMultisection⟧. At a reachable point outside it, the transported point $t(\varphi)$ lies in $U(x) \setminus V$, where all sections vanish. The count at a point where all sections vanish is the zero multisection ⟦Chapter13/AtomicMultisection · SBLocalization.AtomicData.count_eq_zeroMultisection⟧: it is $1$ at $0$ and $0$ elsewhere.
4. *So the domain support lies in the saturation of $\operatorname{cl}V$* ⟦Chapter13/AtomicMultisection · SBLocalization.AtomicData.domSupp_mult_subset⟧, which is closed.
5. *Near a reachable point $y_0$* ⟦Chapter13/AtomicMultisection · SBLocalization.AtomicData.exists_isLocalRepOn_transport⟧.
   - Choose $\varphi_0$ from $y_0$ into $U(x)$. The target map is a local sc-diffeomorphism at $\varphi_0^{-1}$, so there are an open $V_2 \ni y_0$ and an sc-smooth $\tau : V_2 \to \mathbf X$ with $t(\tau(z)) = z$ and $\tau(y_0) = \varphi_0^{-1}$.
   - On $O = V_2 \cap (s \circ \tau)^{-1}(U(x))$, which is open and contains $y_0$, the sections $s'_i(z) = \mu(\tau(z), s_i(s(\tau(z))))$ are sc⁺, being transported sections in the sense of §XIII.9.
   - With weights $|I|^{-1}$ they represent the multisection. At $w$ over $z \in O$, use the morphism $\tau(z)^{-1}$ from $z$ into $U(x)$ in the count.
6. *Local section structures.* A local section structure at every reachable point ⟦Chapter13/AtomicMultisection · SBLocalization.AtomicData.hasLocalSectionStructure_of_reach⟧. At every point outside the saturation of $\operatorname{cl}V$, the single zero section on the complement ⟦Chapter13/AtomicMultisection · SBLocalization.AtomicData.hasLocalSectionStructure_of_not_mem⟧. These two cases cover all points.
7. *Conclusion.* The multisection of the data is an sc⁺-multisection when $I \neq \emptyset$ ⟦Chapter13/AtomicMultisection · SBLocalization.AtomicData.isScPlusMultisection_mult⟧, and it is atomic ⟦Chapter13/AtomicMultisection · SBLocalization.AtomicData.isAtomic_mult⟧.

**Witnesses.**
- *Atomic neighbourhoods exist inside every open set* ⟦Chapter13/AtomicMultisection · SBLocalization.exists_atomicNbhd⟧. For $x$ in an open $W$ there are a natural representation on $U(x) \subset W$ with the properness property and an invariant open $V \ni x$ with $\operatorname{cl}V \subset U(x)$. This uses Theorem 7.1.13 and the shrinking in the proof of Theorem 7.5.7 (Part VII).
- *The zero section at any point* ⟦Chapter13/AtomicMultisection · SBLocalization.AtomicData.zero⟧. One index, the zero section, on such a neighbourhood. Its multisection is the zero multisection ⟦Chapter13/AtomicMultisection · SBLocalization.AtomicData.zero_mult⟧.
- So *the zero multisection is atomic*, at every point ⟦Chapter13/AtomicMultisection · SBLocalization.isAtomic_zeroMultisection⟧.

**Atomic on a neighbourhood with the natural action** (extra) ⟦Chapter13/AtomicSum · SBLocalization.AtomicDataOn⟧ ⟦Chapter13/AtomicSum · SBLocalization.IsAtomicOn⟧. This is Definition 13.5.1 with $U(x)$ a neighbourhood with the natural action (§XIII.1) and proper closure, in place of the domain of a natural representation.
- The sets of a good system are of this kind, and they need not be connected. The first proof of Theorem 13.5.7 produces atomic pieces on such sets. A second proof shrinks them to connected components and gives pieces atomic in the sense of Definition 13.5.1 (§XIII.30).
- The count ⟦Chapter13/AtomicSum · SBLocalization.AtomicDataOn.count⟧, reachability ⟦Chapter13/AtomicSum · SBLocalization.AtomicDataOn.Reach⟧ and condition (3) ⟦Chapter13/AtomicSum · SBLocalization.AtomicDataOn.IsRelated⟧ are as above.
- Atomic data on the domain of a natural representation are atomic data in this sense ⟦Chapter13/AtomicSum · SBLocalization.AtomicData.toOn⟧: the domain with the representation is a neighbourhood with the natural action. So atomic implies atomic in this sense ⟦Chapter13/AtomicSum · SBLocalization.IsAtomic.isAtomicOn⟧, and the zero multisection is a witness.

*Restated*: $U(x)$ is the domain of a natural representation, and $V$ is invariant under the $\Phi(g)$. The count is shown to be independent of $\varphi$. Condition (2) is the data of a symmetric structure.

**Remark 13.5.2** (p. 630) is prose. It says that atomic multisections are built from one section moved around by $G_x$, and that bump functions suffice, not partitions of unity. Theorems 13.5.4–13.5.6 below use bump functions only, as the remark says. Theorem 13.5.7 uses partitions of unity.

### XIII.26 Theorem 13.5.3 (2017: Theorem 13.6): atomic sc⁺-multisections are structurable

The text constructs a structure for an atomic $\Lambda$ in four cases:
- points of $U(x_0)$, with index set $I_{x_0}$;
- points near which $\Lambda$ is trivial, with $\{*\}$;
- the remaining points, through a morphism $\varphi_x$ into $\operatorname{cl}V(x_0)$;
- and correspondences between all pairs.

It closes with "one easily verifies" that the sections are compatible. The formalization reorganizes the cases around one closed saturated set $Z$ and one function $H$, and verifies all compatibilities from two properties of $H$.

**General tools.**
- *The full correspondence* ⟦Chapter13/AtomicStructurable · SBLocalization.IndexCorr.full⟧. $[I \leftarrow I \times I' \to I']$ for nonempty finite $I$, $I'$, built on the diagram ⟦Chapter13/AtomicStructurable · SBLocalization.IndexDiagram.full⟧.
  - Its fibres have the sizes $|I'|$ and $|I|$ ⟦Chapter13/AtomicStructurable · SBLocalization.IndexDiagram.card_fst_fiber⟧ ⟦Chapter13/AtomicStructurable · SBLocalization.IndexDiagram.card_snd_fiber⟧.
  - It is fixed by $\sharp$ up to the order of factors ⟦Chapter13/AtomicStructurable · SBLocalization.IndexCorr.swap_full⟧, and by the bi-action ⟦Chapter13/AtomicStructurable · SBLocalization.IndexCorr.biact_full⟧.
- *Correspondences of bijections.*
  - The bi-action on $[\mathrm{id}, e]$ is $[\mathrm{id}, g' e g^{-1}]$ ⟦Chapter13/AtomicStructurable · SBLocalization.IndexCorr.biact_ofEquiv⟧.
  - $\sharp$ of $[\mathrm{id}, e]$ is $[\mathrm{id}, e^{-1}]$ ⟦Chapter13/AtomicStructurable · SBLocalization.IndexCorr.swap_ofEquiv⟧.
  - $[\mathrm{id}, e]$ saturates a relation $R$ iff $R(i, e(i))$ for all $i$ ⟦Chapter13/AtomicStructurable · SBLocalization.IndexCorr.sat_ofEquiv⟧.
- *Locally constant choices* ⟦Chapter13/AtomicStructurable · SBLocalization.eventually_eq_of_existsUnique⟧. Let $f$ and $g_h$, for $h$ in a finite set, be continuous maps into a Hausdorff space on an open set, and suppose $f(z) = g_h(z)$ for exactly one $h$ at every $z$. Then the $h$ with $f(z_0) = g_h(z_0)$ still works near $z_0$. For each of the finitely many other $h'$, $g_{h'}(z_0) \neq f(z_0)$, and this persists near $z_0$ by Hausdorffness and continuity. The equality for $h$ itself is then forced by existence.
- *Locally constant functions are constant on components* ⟦Chapter13/AtomicStructurable · SBLocalization.eq_of_mem_connectedComponentIn⟧. The level sets are open in the open set, so each component lies in one of them.
- *Composition rules for $\mu$*, in the total form of §XIII.9: composition ⟦Chapter13/SymmetricOn · SBLocalization.fibAct_comp⟧, units ⟦Chapter13/SymmetricOn · SBLocalization.fibAct_unit⟧, and inverses ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.fibAct_inv_fibAct⟧ ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.fibAct_fibAct_inv⟧.
  - The transported section of §XIII.9 is the action at each point ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.transportSection_eq_fibAct⟧.
  - $\varphi \circ (\varphi^{-1} \circ \chi) = \chi$ ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.comp_inv_comp⟧.

**The data of the proof** ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData⟧.
- Atomic data $D$ related to $\Lambda$, at $x_0$, with $I \neq \emptyset$.
- A good system $\mathcal U_0$.
- For every $y$ in $Z = \pi^{-1}\pi(\operatorname{cl}V(x_0))$: an open $O(y) \ni y$ and an sc-smooth $\tau_y : O(y) \to \mathbf X$ with $t(\tau_y(z)) = z$ and $s(\tau_y(z)) \in U(x_0)$, along which the atomic sections transport to sc⁺-sections.

*Existence* ⟦Chapter13/AtomicStructurable · SBLocalization.exists_atomicStructData⟧: for every atomic $\Lambda$ with data $D$ and every good system. A point of $Z$ is reachable, and the local structure of §XIII.25 (step 5) gives $O(y)$ and $\tau_y$. $\tau_y$ is the text's $(s|_{U(\varphi_x)})^{-1}$, inverted.

**The set $Z$.** $Z$ ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.Z⟧ is the saturation of $\operatorname{cl}V(x_0)$.
- It is closed ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.isClosed_Z⟧, by §XIII.25.
- It is saturated: the source of a morphism is in $Z$ iff its target is ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.mem_Z_iff_of_mor⟧.
- Off $Z$, $\Lambda$ is trivial (§XIII.25).

The text's four cases become two: $y \in Z$ and $y \notin Z$. The text's points of $U(x_0)$ outside $Z$, and its points with a neighbourhood where $\Lambda$ is trivial, fall into the second case. Its points of $U(x_0)$ in $Z$ use $\tau_y$ like every other point of $Z$, with no special treatment.

**The partner function $H$.** Fix $y, y' \in Z$. Write:
- $\sigma_y(z) = s(\tau_y(z)) \in U(x_0)$ ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.σ⟧;
- $\operatorname{Dom}(y, y')$ for the morphisms from $O(y)$ to $O(y')$ ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.Dom⟧, an open set.

For $\psi \in \operatorname{Dom}(y, y')$ the conjugate
$$\operatorname{conj}(\psi) = \tau_{y'}(t\psi)^{-1} \circ \psi \circ \tau_y(s\psi)$$
⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.conj⟧ runs from $\sigma_y(s\psi)$ to $\sigma_{y'}(t\psi)$ ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.src_conj⟧ ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.tgt_conj⟧. These are two points of $U(x_0)$, so:
1. *$\operatorname{conj}(\psi) = \Gamma(h, \sigma_y(s\psi))$ for a unique $h \in G_{x_0}$* ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.existsUnique_rel⟧. Existence is the surjectivity of the natural representation. Uniqueness is its injectivity: $\Gamma(\cdot, z)$ is injective for each $z$.
2. *$H(\psi)$* ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.H⟧ is this $h$, and $1$ when $y \notin Z$, $y' \notin Z$ or $\psi \notin \operatorname{Dom}(y, y')$ ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.H_far⟧. It is characterized by its defining equation ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.H_spec⟧, and any $h$ satisfying it is $H(\psi)$ ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.H_eq_of_rel⟧.
3. *Functorial* ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.H_comp⟧ ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.H_unit⟧ ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.H_inv⟧:
   - $H(\psi_1 \circ \psi_2) = H(\psi_1)H(\psi_2)$, because the conjugates compose, the inner $\tau$'s cancelling, and $\Gamma(h_1, \cdot) \circ \Gamma(h_2, \cdot) = \Gamma(h_1h_2, \cdot)$;
   - $H(1_z) = 1$;
   - $H(\psi^{-1}) = H(\psi)^{-1}$.

   Each follows by uniqueness in step 1.
4. *Locally constant* ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.H_eventually⟧. The conjugate depends continuously on $\psi$ ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.continuousOn_conj⟧, since $\tau_y$, $\tau_{y'}$, composition and inversion are continuous. Each $\psi \mapsto \Gamma(h, \sigma_y(s\psi))$ is continuous. $G_{x_0}$ is finite, and the space of morphisms is Hausdorff. Apply the tool on locally constant choices.

**The homomorphisms $\gamma_y$.** For $y \in Z$, the morphism $\Gamma_0(g, y)$ of the natural representation of $\mathcal U_0$ at $y$ lies in $\operatorname{Dom}(y, y)$ ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.Γ₀_mem_Dom⟧. Define
$$\gamma_y(g) = H(\Gamma_0(g, y))$$
⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.γ⟧ ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.γ_apply⟧.
- It is a homomorphism $G_y \to G_{x_0}$: units by $H(1) = 1$, products by functoriality.
- It is trivial for $y \notin Z$ ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.γ_far⟧.
- It is the text's $\gamma_x$ in both of the text's cases. For $y \in U(x_0)$ it is defined by $\Gamma^y(g, y) = \Gamma^{x_0}(\gamma_y(g), y)$ when $\tau_y$ is the unit. For the other points of $Z$ it is the conjugation $\varphi_x \circ g \circ \varphi_x^{-1}$.

**The good system.** The neighbourhoods must be small enough that $H$ is constant along the natural action.
1. *$W_n(y)$* ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.Wn⟧: the points $z$ of $U_0(y) \cap O(y)$ with $g * z \in O(y)$ and $H(\Gamma_0(g, z)) = \gamma_y(g)$ for all $g$.
2. *It is a neighbourhood of $y$* ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.eventually_Wn⟧. For each of the finitely many $g$, local constancy of $H$ at $\Gamma_0(g, y)$, with continuity of $z \mapsto \Gamma_0(g, z)$, gives a neighbourhood. Intersect them.
3. *$W(y)$* ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.W⟧ is the interior of $W_n(y)$ for $y \in Z$, and $Z^c$ for $y \notin Z$. It is open ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.isOpen_W⟧ and contains $y$ ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.mem_W⟧.
4. *$M(y)$* ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.M⟧ is the invariant core of $U_0(y)$ in $W(y)$ (§XIII.1). It has the action of $\mathcal U_0$ at $y$.
5. *The good system* ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.𝒰⟧ is $(M(y))$, by the lemma of §XIII.10. Its properties:
   - $U(y) \subset W(y)$ ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.U_subset_W⟧;
   - $U(y) \subset W_n(y)$ for $y \in Z$ ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.mem_Wn⟧, hence $U(y) \subset O(y)$ ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.U_subset_O⟧;
   - $U(y) \cap Z = \emptyset$ for $y \notin Z$ ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.not_mem_Z⟧;
   - $H(\Gamma(g, z)) = \gamma_y(g)$ for $z \in U(y)$, $y \in Z$ ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.W_cond⟧;
   - morphisms between $U(y)$ and $U(y')$ lie in $\operatorname{Dom}(y, y')$ ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.mor_subset_Dom⟧.

**The sections** ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.sec⟧. The index set is $I = I_{x_0}$ at every point.
- For $y \in Z$, the transported sections $z \mapsto \mu(\tau_y(z), s_i(\sigma_y(z)))$ ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.sec_of_mem⟧ ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.sec_apply⟧. They lie over the right points ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.P_s_σ⟧.
- For $y \notin Z$, the zero sections ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.sec_of_not_mem⟧.
- *Compatibility through $H$* ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.sec_compat⟧. For $y, y' \in Z$ and $\psi \in \operatorname{Dom}(y, y')$:
$$\text{sec}_{y'}(H(\psi)\cdot i)(t\psi) = \mu(\psi, \text{sec}_y(i)(s\psi)).$$
  Proof:
  1. Write $\psi = \tau_{y'}(t\psi) \circ \Gamma(H(\psi), \sigma_y(s\psi)) \circ \tau_y(s\psi)^{-1}$.
  2. Apply the composition rule for $\mu$.
  3. Apply the equivariance of the atomic sections at $\sigma_y(s\psi)$.
- *Vanishing off $Z$* ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.sec_eq_zero⟧. At a point $z \notin Z$ every section is zero. For $y \in Z$, $\sigma_y(z) \in U(x_0)$ lies outside $V(x_0)$, since $z \notin Z$, so the atomic sections vanish there.

**The symmetric structures** ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.S⟧ have index set $I$, with $G_y$ acting through $\gamma_y$, and the sections above.
- *Sc⁺:* transported sections are sc⁺ by the data. Zero sections are sc⁺.
- *Equivariance:* for $y \in Z$, compatibility at $\Gamma(g, z)$ with $H(\Gamma(g, z)) = \gamma_y(g)$, which is the role of $W_n$. For $y \notin Z$, the zero sections are equivariant for any action.
- *Representation by the count* (Definition 13.2.5):
  - for $y \in Z$, the count of $\Lambda$ at $w$ over $z \in U(y)$ is that of $\mu(\tau_y(z)^{-1}, w)$ over $\sigma_y(z) \in U(x_0)$, by Definition 13.5.1 (3), and $\mu(\tau_y(z), \cdot)$ carries the one count to the other;
  - for $y \notin Z$, $\Lambda$ is trivial on $U(y)$ and the zero sections represent it, whatever $|I| \ge 1$ is.

The decoration is $(\mathcal U, S)$ ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.dec⟧.

**The correspondences** ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.corr⟧. For $\varphi$ from $U(y)$ to $U(y')$:
$$\tau_{y,y'}(\varphi) = \begin{cases}[I \xleftarrow{\mathrm{id}} I \xrightarrow{H(\varphi)} I] & \text{if } y \in Z \Leftrightarrow y' \in Z,\\ [I \leftarrow I \times I \to I] & \text{otherwise}\end{cases}$$
⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.corr_of_iff⟧ ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.corr_of_not_iff⟧.

When exactly one of $y, y'$ lies in $Z$, the morphisms between $U(y)$ and $U(y')$ join points outside $Z$. One of the two sets misses $Z$, and $Z$ is saturated. There all sections vanish, and the full correspondence is compatible.

**Definition 13.3.4** ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.isCorrespondence⟧.
1. *Locally constant.* $H$ is locally constant on the morphisms between $U(y)$ and $U(y')$ ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.H_eventually'⟧. The full correspondence is constant.
2. *Finitely many values.* $G_{x_0}$ is finite.
3. *Equivariance* ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.H_biact⟧. $H(g' * \varphi * g) = \gamma_{y'}(g')H(\varphi)\gamma_y(g)^{-1}$, by functoriality and the condition of $W_n$. With the law for the bi-action on $[\mathrm{id}, e]$ this is Definition 13.3.4 (2). The full correspondence is fixed by the bi-action.
4. *Compatibility.* On a component $\Sigma$ of $\mathcal U(y, y')$, $H$ is constant, since it is locally constant. So for $\varphi \in \Sigma$ the relation saturated by $[\mathrm{id}, H(\varphi)]$ holds at every $\psi \in \Sigma$, by the compatibility of the sections through $H(\psi) = H(\varphi)$. Across $Z$ and $Z^c$, all sections vanish.

**Definition 13.3.6** ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.tau⟧.
- *Diagonal:* $\tau_{y,y}(\Gamma(g, z)) = [\mathrm{id}, H(\Gamma(g, z))] = [\mathrm{id}, \gamma_y(g)]$, by the condition of $W_n$. This is $[\mathrm{id}, g]$ for the action through $\gamma_y$.
- *Swap:* $[\mathrm{id}, H(\varphi^{-1})] = [\mathrm{id}, H(\varphi)^{-1}] = [\mathrm{id}, H(\varphi)]^\sharp$, and the full correspondence is its own swap up to the order of factors.

So $\Lambda$ is structurable ⟦Chapter13/AtomicStructurable · SBLocalization.AtomicStructData.isStructurable⟧.

*Where the formal proof departs from the text.* The text uses $\{*\}$ with the zero section where $\Lambda$ is trivial, and correspondences $[\{*\} \leftarrow I \to I]$ to such points. The formalization uses $I$ with zero sections and the full correspondence. Both are structures in the sense of Definition 13.3.6. This is a different witness, not a different statement.

**Theorem 13.5.3** (narrower), p. 630 ⟦Chapter13/AtomicStructurable · SBLocalization.theorem_13_5_3_of_goodSystem⟧. If $X$ has a good system, every atomic sc⁺-multisection is structurable.

*The added hypothesis*, that a good system exists, is not derived from the text, whose statement assumes nothing on $X$. It is necessary: for atomic $\Lambda$, structurable is equivalent to the existence of a good system ⟦Chapter13/AtomicStructurable · SBLocalization.theorem_13_5_3⟧, since Definition 13.3.6 includes one. Its witness is Theorem 13.1.8 for paracompact $|X|$ (§XIII.6) ⟦Chapter13/GoodSystemExistence · EpGroupoid.theorem_13_1_8⟧, which gives the form ⟦Chapter13/AtomicStructurable · SBLocalization.theorem_13_5_3_of_paracompact⟧.

As printed, the theorem puts no hypothesis on $X$, but a structurable sc⁺-multisection contains a good system by Definition 13.3.6, so the statement needs one; Chapter 13 has no standing assumption that supplies it, and the formal statement names it (narrower, with the added hypothesis shown necessary). The text's proof begins by choosing neighbourhoods with the natural action and the properness property at every point, which is a good system in all but condition (3).

**The local alternative, and a parametric form.** A first Lean form of the theorem isolates the local part of the proof.
- *The local alternative* ⟦Chapter13/AtomicStructurableLocal · SBLocalization.AtomicData.IsLocallyTransported⟧ ⟦Chapter13/AtomicStructurableLocal · SBLocalization.theorem_13_5_3_local⟧. For atomic data of $\Lambda$, at every point $y$ one of two things holds:
  - on an open $O \ni y$, $\Lambda$ is represented by the atomic sections transported along an sc-smooth $\tau$ into $U(x_0)$, with weights $|I|^{-1}$;
  - $\Lambda$ is trivial on an open $O \ni y$.

  This is §XIII.25 (steps 3 and 5), split by reachability.
- *Remark on the parametric form.* The same file states Theorem 13.5.3 for any predicate "structurable" that holds for every sc⁺-multisection with atomic data whose local alternatives hold everywhere ⟦Chapter13/AtomicStructurableLocal · SBLocalization.theorem_13_5_3_hyp⟧. That hypothesis is satisfiable, with "structurable" read as "is an sc⁺-multisection" ⟦Chapter13/AtomicStructurableLocal · SBLocalization.theorem_13_5_3_hyp_witness⟧. The last clause of Theorem 13.5.5 is stated in the same form ⟦Chapter13/AtomicStructurableLocal · SBLocalization.theorem_13_5_5_structurable_hyp⟧. The proof above supersedes the hypothesis for the predicate of Definition 13.3.6. The parametric clause is still the route by which the last clause of Theorem 13.5.5 is derived (§XIII.28), with Theorem 13.5.3 substituted for the parameter.

### XIII.27 Theorem 13.5.4 (2017: Theorem 13.7): Construction I

**Symmetric families** ⟦Chapter13/AtomicConstruction · SBLocalization.SymmetricFamily⟧. These are the input of Theorem 13.5.5 (p. 633): for a natural representation of $G_x$ on $U(x)$,
- a finite index type $I$ with a $G_x$-action;
- sc⁺-sections $s_i$ of $W \to X$, global, viewing $X$ as an M-polyfold, with support in $U(x)$;
- equivariance $s_{g(i)}(g * z) = \mu(\Gamma(g, z), s_i(z))$ for $z \in U(x)$.

Construction I produces such families. They vanish off $V$, which is stronger than "on $U(x) \setminus V$", since they are global and supported in $V$.

**Auxiliary facts on $\mu$ and the auxiliary norm.**
- $\mu(\varphi, \cdot)$ preserves the level-$1$ part of the fibres ⟦Chapter13/AtomicConstruction · SBLocalization.mem_oneSet_μ⟧ ⟦Chapter13/AtomicConstruction · SBLocalization.mem_oneSet_of_μ⟧, in both directions, since it is a strong bundle isomorphism of fibres.
- An auxiliary norm $N$ (Definition 8.3.5, 2021 numbering; Part VIII) is invariant: $N(\mu(\varphi, w)) = N(w)$ ⟦Chapter13/AtomicConstruction · SBLocalization.normW_μ⟧. This is the compatibility of auxiliary norms with the structure maps.
- The zero vector is at level $1$ ⟦Chapter13/AtomicConstruction · SBLocalization.fiberZero_mem_oneSet⟧ and has norm $0$ ⟦Chapter13/AtomicConstruction · SBLocalization.normW_fiberZero⟧.

**The family of one seed** ⟦Chapter13/AtomicConstruction · SBLocalization.SymmetricFamily.ofSeed⟧. Let $s_0$ be an sc⁺-section supported in an invariant open $V$ with $\operatorname{cl}V \subset U(x)$. Take:
- $I = G_x$, acting on itself by left multiplication;
- $s_g(z) = \mu(\Gamma(g, g^{-1} * z), s_0(g^{-1} * z))$ on $U(x)$, and $0$ off $U(x)$.

These are the terms of the average of Part XII. They are global sc⁺-sections supported in $\Phi(g)(\operatorname{supp}s_0) \subset V$. Their values ⟦Chapter13/AtomicConstruction · SBLocalization.SymmetricFamily.ofSeed_s⟧:
- $s_1 = s_0$ on $U(x)$ ⟦Chapter13/AtomicConstruction · SBLocalization.SymmetricFamily.ofSeed_one⟧;
- the family vanishes off $V$ ⟦Chapter13/AtomicConstruction · SBLocalization.SymmetricFamily.ofSeed_vanish⟧;
- if $N(s_0(y)) \le b$ everywhere, then $N(s_g(y)) \le b$ everywhere ⟦Chapter13/AtomicConstruction · SBLocalization.SymmetricFamily.ofSeed_normW_le⟧, by invariance of $N$.

Equivariance, the text's (13.8), is $s_{gh}(g * z) = \mu(\Gamma(g, z), s_h(z))$. It follows from $\Gamma(g, h * z) \circ \Gamma(h, z) = \Gamma(gh, z)$ and the composition law of $\mu$. The text's map $\tau : G_x \to \operatorname{Per}(G_x)$ is the left multiplication action.

**Theorem 13.5.4 (1)** (narrower), p. 632 ⟦Chapter13/AtomicConstruction · SBLocalization.theorem_13_5_4_1⟧. Assume:
- $X$ admits bump functions in the pointwise reading;
- $x$ is smooth;
- $U(x)$ is the domain of a natural representation with the properness property;
- $V \ni x$ is open, invariant, with $\operatorname{cl}V \subset U(x)$;
- $w \in W_x$ is smooth.

Then there is a symmetric family vanishing off $V$ with $s_{i_0}(x) = w$ for some $i_0$.

*Proof.*
1. An auxiliary norm of Part I exists, by Proposition 5.1.3 (Part V).
2. Part I's Lemma 5.3.3 gives an sc⁺-section $s_0$ with $s_0(x) = w$, supported in $V$ ⟦Chapter5/BumpFunctions · lemma_5_3_3⟧. Its bump-function hypothesis on the object M-polyfold comes from the pointwise reading on the ep-groupoid, by Theorem 12.3.2 (1) (Part XII). This is the text's "construct in local coordinates an sc⁺-section … multiply by a bump function".
3. The family of the seed $s_0$, with $i_0 = 1$.

**The cut-off** ⟦Chapter13/AtomicConstruction · SBLocalization.exists_cutoff⟧. For an sc⁺-section $s$ on an open $O \ni x$ and an open $V \ni x$, there is an sc⁺-section $s_0$ of $W \to X$ with these properties:
- it is supported in $V$;
- it equals $s$ near $x$;
- it vanishes off $V \cap O$;
- $N(s_0(y)) \le N(s(y))$ on $O$ for every auxiliary norm $N$.

*Proof.*
1. Proposition 5.5.3 (Part V) gives an sc-smooth $\beta : X \to [0, 1]$ with $\beta = 1$ near $x$ and $\operatorname{supp}\beta \subset V \cap O$.
2. $s_0 = \beta \cdot s$, with $s$ extended by zero off $O$. It vanishes where $\beta = 0$ ⟦Chapter13/AtomicConstruction · SBLocalization.sectionSmul_eq_fiberZero⟧.
3. It is sc⁺: on $O$ as a product of an sc-smooth function and an sc⁺-section, and off the closed support of $\beta$ as the zero section. These two open sets cover $X$.
4. The norm bound: $N(\beta(y)s(y)) = |\beta(y)|N(s(y)) \le N(s(y))$.

The text asks for $\beta(x) = 1$ "with arbitrarily small support". The conclusion "$s_{i_0} = s$ near $x$" needs $\beta = 1$ near $x$, which Proposition 5.5.3 provides.

**Theorem 13.5.4 (2)** (narrower), p. 632 ⟦Chapter13/AtomicConstruction · SBLocalization.theorem_13_5_4_2⟧. For an sc⁺-section $s$ on an open $O \ni x$, there is a symmetric family vanishing off $V$ with $s_{i_0} = s$ near $x$. *Proof*: the family of the seed given by the cut-off, with $i_0 = 1$.

*Narrower* only through the pointwise reading of bump functions, as in Theorem 12.3.3 (Part XII). The conclusions are stronger than printed: global sections, vanishing off $V$. The properness property in both parts, and the smoothness of $x$ in (2), are kept and not used.

### XIII.28 Theorem 13.5.5 (2017: Theorem 13.8): Construction II

**Step 1: an invariant $V$** ⟦Chapter13/AtomicConstruction · SBLocalization.SymmetricFamily.exists_vanishing_nbhd⟧. For a symmetric family on $U(x)$ there is an open invariant $V \ni x$ with $\operatorname{cl}V \subset U(x)$ off which every section vanishes.
1. $K = \{x\} \cup \bigcup_i\operatorname{supp}s_i$ is closed, and lies in $U(x)$ since the supports do.
2. The object space is Hausdorff and paracompact, hence normal. There is an open $V_0 \supset K$ with $\operatorname{cl}V_0 \subset U(x)$.
3. $V = \bigcap_{g \in G_x}(U(x) \cap \Phi(g)^{-1}(V_0))$ is open, contains $x$, and is invariant. Its closure lies in $\operatorname{cl}V_0 \subset U(x)$.
4. Every section vanishes off $V$. Equivariance gives $s_{g(i)}(g * z) = 0$ iff $s_i(z) = 0$ ⟦Chapter13/AtomicConstruction · SBLocalization.SymmetricFamily.eq_zero_iff⟧, since $\mu(\Gamma(g, z), \cdot)$ is injective and maps $0$ to $0$. A point $z \in U(x) \setminus V$ has some $g$ with $g * z \notin V_0$. Then $g * z \notin \operatorname{supp}s_{g(i)}$, so $s_{g(i)}(g * z) = 0$ and $s_i(z) = 0$. A point outside $U(x)$ is outside every support.

This is condition (ii) of the text's proof, which takes such a $V(x)$ as given.

**Step 2: the atomic data** ⟦Chapter13/AtomicConstruction · SBLocalization.AtomicData.ofFamily⟧. The family restricted to $U(x)$, with this $V$, is atomic data in the sense of §XIII.25. Global sc⁺-sections are sc⁺ on $U(x)$.

**Theorem 13.5.5** (narrower), p. 633 ⟦Chapter13/AtomicConstruction · SBLocalization.theorem_13_5_5⟧. For a symmetric family on $U(x)$, with $U(x)$ having the properness property and $I \neq \emptyset$, there is a unique $\Lambda$ with these properties:
- it is atomic;
- it is trivial over the points outside the saturation of $U(x)$;
- over $U(x)$, $\Lambda(w) = |I|^{-1}\#\{i : s_i(P(w)) = w\}$.

*Proof.*
1. *Existence.* The multisection of the data of step 2. It is atomic, by §XIII.25. It is trivial off the saturation of $\operatorname{cl}V$, which lies in the saturation of $U(x)$. Over $U(x)$ it is the count.
2. *Uniqueness.* Let $\Lambda$ have the three properties, and $w$ a vector.
   - If $P(w)$ is reachable through $\varphi$, then $\Lambda(w) = \Lambda(\mu(\varphi, w))$, since $\Lambda$ is a functor. That is the count, by the third property.
   - Otherwise $P(w)$ is outside the saturation of $U(x)$, and $\Lambda$ is trivial there by the second property.

   In both cases $\Lambda(w)$ is the value of the multisection of the data.

*Narrower* by $I \neq \emptyset$. The text does not state it, and the printed formula presupposes it. With $I = \emptyset$ the formula gives $\Lambda = 0$ on all vectors over $U(x)$, which is not an sc⁺-multisection, since the weights over a point sum to $1$. For atomic $\Lambda$ it is automatic (§XIII.25), and the families of Construction I have $I = G_x$ (§XIII.27).

"Supported in the saturation of $U(x)$" is read as triviality over the points not isomorphic to a point of $U(x)$. This is the text's definition of $\Lambda$ off the reachable points. Bump functions and the smoothness of $x$ are kept and not used.

**The last clause: $\Lambda$ is structurable** (narrower), p. 633 ⟦Chapter13/AtomicStructurable · SBLocalization.theorem_13_5_5_structurable⟧. Given a good system, the atomic $\Lambda$ of Construction II is structurable. It is the parametric form of §XIII.26 ⟦Chapter13/AtomicStructurableLocal · SBLocalization.theorem_13_5_5_structurable_hyp⟧ with Theorem 13.5.3 substituted, as the text derives it ("We have already established that they are structurable"). The added hypothesis is that of Theorem 13.5.3, with the same witness.

### XIII.29 Theorem 13.5.6 (2017: Theorem 13.9): atomic multisections through a vector, and with a bound

**Two facts about the multisection of atomic data.**
- *A norm bound* ⟦Chapter13/AtomicConstruction · SBLocalization.AtomicData.pointwiseNorm_mult_le⟧. If $N(s_i(z)) \le b$ for all $i$ and $z \in U(x)$, with $b \ge 0$, then the pointwise norm of Definition 13.2.3 (§XIII.8) satisfies $N(\Lambda)(y) \le b$ for every $y$. Every vector with positive weight falls in one of two cases:
  - over a reachable point, it is $\mu(\varphi^{-1}, s_i(t\varphi))$ for some $i$, and $N$ is invariant;
  - otherwise, it is $0$.
- *The local structure on $U(x)$* ⟦Chapter13/AtomicConstruction · SBLocalization.AtomicData.isLocalRepOn_mult⟧. Over $U(x)$ the sections of the data, enumerated, with weights $|I|^{-1}$, are a local section structure of the multisection.

**Theorem 13.5.6, first part** (narrower), p. 634 ⟦Chapter13/AtomicConstruction · SBLocalization.theorem_13_5_6_1⟧. Let $w \neq 0$ be smooth over $x$, and $U(x)$ the domain of a natural representation. Then there is an atomic $\Lambda$ with:
1. $\operatorname{dom-supp}(\Lambda)$ in the saturation of $U(x)$;
2. $\Lambda(\mu(g, w)) > 0$ for every $g \in G_x$.

*Proof.*
1. Inside $U(x)$ choose a natural representation $U'(x)$ with the properness property and an invariant $V$ with $\operatorname{cl}V \subset U'(x)$ (§XIII.25).
2. $x$ is smooth, since $w$ is.
3. Construction I (1) gives a family through $w$, vanishing off $V$.
4. Its atomic data give $\Lambda$, the multisection of the data, with $I = G_x$.
5. The domain support lies in the saturation of $\operatorname{cl}V$, so in that of $U(x)$.
6. $\Lambda(\mu(g, w)) = \Lambda(w)$, since $\Lambda$ is a functor. That is the count at $w$, which is positive because $s_1(x) = w$.

The text's "$\pi^{-1}(U(x))$" is read as the saturation of $U(x)$, and "$\Lambda(g * w)$" as $\Lambda(\mu(g, w))$.

**Theorem 13.5.6, second part** (narrower), p. 634 ⟦Chapter13/AtomicConstruction · SBLocalization.theorem_13_5_6_2⟧. Let $N$ be an auxiliary norm, $s$ an sc⁺-section on $U(x)$, and $\varepsilon > 0$. Then there is an atomic $\Lambda$ with:
1. domain support in the saturation of $U(x)$;
2. $N(\Lambda)(y) \le N(s(x)) + \varepsilon$ for all $y$;
3. a local section structure on an open $O \ni x$ one of whose sections equals $s$ on $O$, with positive weight.

*Proof.*
1. Let $b = N(s(x)) + \varepsilon$. The set $O_1 = U(x) \cap \{N(s(\cdot)) < b\}$ is open and contains $x$: $N$ is continuous on the level-$1$ part and $s$ is sc⁺.
2. Inside $O_1$ choose $U'(x)$ and $V$ as in the first part.
3. The cut-off of $s$ on $U'(x)$ gives a seed $s_0$ equal to $s$ near $x$. Its norm is $\le N(s(y)) < b$ on $U'(x)$, and $0$ elsewhere, so $\le b$ everywhere.
4. The family of the seed keeps the bound, and its atomic data give $\Lambda$, with the norm bound by the first fact above.
5. Near $x$, $s_1 = s_0 = s$. The local structure on $U'(x)$, restricted to $U'(x) \cap O'$ with $O'$ the set where $s_0 = s$, contains $s$ with weight $|G_x|^{-1} > 0$.

"Whose local section structure near $x$ contains $s$ with positive weight" is read as the third property.

**Both parts** ⟦Chapter13/AtomicConstruction · SBLocalization.theorem_13_5_6⟧. *Narrower* only through the pointwise reading of bump functions. The paracompactness of $|X|$ is kept and not used. The text uses it for the existence of $N$ (Theorem 12.2.2), and here $N$ is given.

### XIII.30 Theorem 13.5.7 (2017: Theorem 13.10): decomposition into commensurable atomic pieces

**Tools.**
- *The pieces as data over $c$* ⟦Chapter13/AtomicSum · SBLocalization.CommData.smulFunOver⟧. For a structured tuple $T$ and an sc-smooth function $\beta$ invariant along morphisms, the sections $\beta s^x_i$ are data over the choice $c$ of $T$ (§XIII.24) for $\beta \odot \Lambda$. This is Lemma 13.3.14 (§XIII.16), with the same index sets and correspondences.
- *$\beta \odot \Lambda$ is trivial where $\beta = 0$* ⟦Chapter13/AtomicSum · SBLocalization.multisectionSmulFun_of_eq_zero⟧.
- *Shrinking in the orbit space* ⟦Chapter13/AtomicSum · SBLocalization.exists_orbit_nbhd⟧. For a good system and a point $x$ there is an open $O_x \ni |x|$ in $|X|$ with $\operatorname{cl}O_x \subset |U(x)|$. $|U(x)|$ is open, by Proposition 7.1.8, and $|X|$ is regular, by Lemma 7.3.5 (Part VII).

**Theorem 13.5.7** (stronger), p. 635 ⟦Chapter13/AtomicSum · SBLocalization.theorem_13_5_7⟧. If $X$ has sc-smooth partitions of unity, then for every structured tuple $T = (\Lambda, \mathcal U, S, \tau)$ there are:
- a locally finite family $(\Lambda_j)_{j \in X}$, each atomic on a neighbourhood with the natural action (§XIII.25);
- data over the choice $c$ of $T$ for each $\Lambda_j$;

such that
- the locally finite commensurable sum (§XIII.24) is $\Lambda$;
- its sections are those of $T$ on every $U(x)$;
- its structured class is that of $T$.

*Proof.*
1. *A partition of unity.* For each $x$ take $O_x$ by the shrinking. The sets $\pi^{-1}(O_x)$ form an open saturated cover of $X$. Take an sc-smooth partition of unity of functors $(\beta_j)_{j \in X}$ subordinate to it, with $\operatorname{supp}\beta_j \subset \pi^{-1}(O_j)$.
2. *The pieces.* $\Lambda_j = \beta_j \odot \Lambda$, with data $\beta_js^x_i$ over $c$.
3. *Locally finite* (Definition 13.2.12). Near each point only finitely many $\beta_j$ are nonzero, and $\Lambda_j$ is trivial where $\beta_j = 0$. The neighbourhoods can be taken saturated, because the $\beta_j$ are functors.
4. *The sections.* $\sum_j\beta_j(y)s^x_i(y) = s^x_i(y)$, since $\sum_j\beta_j = 1$. The finite sum is that of §XIII.24, with the zero summands removed.
5. *The sum is $\Lambda$.* The counts of the same sections agree, and the count over $c$ is $\Lambda$ on every $U(x)$.
6. *Each piece is atomic* at $x_j = j$:
   - $U(j)$ with its natural action, and proper closure (good systems);
   - $V = U(j) \cap \pi^{-1}(O_j)$, open and invariant, with $\operatorname{cl}V \subset U(j)$ by Lemma 13.1.1 (§XIII.1);
   - sections $\beta_js^j_i$, which vanish on $U(j) \setminus V$, where $\beta_j = 0$;
   - condition (3) at reachable points is the count of $\Lambda_j$ transported along $\varphi$;
   - off the saturation of $U(j)$, $\beta_j = 0$, since $\operatorname{cl}O_j \subset |U(j)|$, so $\Lambda_j$ is trivial.
7. *The classes are equal.* The commensurable sum's tuple and $T$ have the same multisection, the same good system and the same index sets. Their correspondences agree after the identity relabelling. So they are equivalent in the sense of Definition 13.3.8, and their classes are equal.

**The text's form** ⟦Chapter13/AtomicSum · SBLocalization.theorem_13_5_7_book⟧. For structurable $\Lambda$ on $X$ with paracompact $|X|$ and sc-smooth partitions of unity, $\Lambda$ has a structured lift that is the locally finite commensurable sum of atomic pieces. Paracompactness is kept and not used.

*Stronger*:
- the decomposition holds for every structured lift, not only one;
- the class equality is literal, through the quotient by Definition 13.3.8;
- the paracompactness of $|X|$ is not used, since regularity of $|X|$, which every ep-groupoid has, suffices for the shrinking.

The text's refinement $(V_j)_{j \in J}$ with points $x_j$ is replaced by the index set $X$ itself, with $V_j = O_j$. The atomic pieces are atomic on neighbourhoods with the natural action, the extra reading of Definition 13.5.1. The sets of a good system need not be domains of natural representations.

**With atomic summands in the sense of Definition 13.5.1** ⟦Chapter13/Theorem1357Atomic · SBLocalization.theorem_13_5_7_isAtomic⟧. The pieces above are atomic on the sets $U(x_j)$ of the good system, which need not be connected. Rerunning the proof with a partition of unity subordinate to smaller sets makes every $\Lambda_j$ atomic on the connected domain of a natural representation with the properness property, which is Definition 13.5.1 as formalized (§XIII.25). The rest of the statement is unchanged: the family is indexed by $X$, it lies over the data of $T$, its commensurable sum is $\Lambda$, its sections are those of $T$ on every $U(x)$, and its structured class is that of $T$.

*Tools.*
- *The connected component is invariant* ⟦Chapter13/Theorem1357Atomic · SBLocalization.mapsTo_Φ_connectedComponentIn⟧. For $g$ in the isotropy of $x$, $\Phi(g)$ maps the component $U^c(x)$ of $x$ in $U(x)$ into itself: the image of $U^c(x)$ is preconnected, contained in $U(x)$, and contains $\Phi(g)(x) = x$.
- *The natural representation on $U^c(x)$* ⟦Chapter13/Theorem1357Atomic · SBLocalization.connRep⟧. The restriction of the natural representation of $U(x)$, with the same $\Phi$ and $\Gamma$, to the open connected invariant set $U^c(x) \ni x$ ⟦Chapter13/Theorem1357Atomic · SBLocalization.connRep_U_subset⟧. It has the properness property when $\operatorname{cl}U(x)$ is proper, since $\operatorname{cl}U^c(x)$ is a closed subset of it ⟦Chapter13/Theorem1357Atomic · SBLocalization.hasPropernessProperty_connRep⟧.
- *Shrinking inside an open set* ⟦Chapter13/Theorem1357Atomic · SBLocalization.exists_orbit_nbhd_of_isOpen⟧. For open $U \ni x$ there is an open $O \ni |x|$ in $|X|$ with $\operatorname{cl}O \subset |U|$: $|U|$ is open by Proposition 7.1.8, and $|X|$ is regular.

*Proof.*
1. *Smaller sets.* For each $x$ take $O_x$ with $\operatorname{cl}O_x \subset |U^c(x)|$, and a partition of unity of functors $(\beta_j)_{j \in X}$ subordinate to the saturated cover $\pi^{-1}(O_x)$.
2. *The pieces, local finiteness, the sections, the sum.* Steps 2–5 of the proof above, word for word: $\Lambda_j = \beta_j \odot \Lambda$ with data $\beta_js^x_i$ over $c$.
3. *Each piece is atomic* at $x_j = j$, on $U^c(j)$:
   - the natural representation $U^c(j)$, with the properness property by the second tool;
   - $V = U^c(j) \cap \pi^{-1}(O_j)$, open and invariant, with $\operatorname{cl}V \subset U^c(j)$ by Lemma 13.1.1 applied to $U^c(j)$;
   - the sections $\beta_js^j_i$ restricted to $U^c(j)$, equivariant and vanishing on $U^c(j) \setminus V$, where $\beta_j = 0$;
   - condition (3) at points of $U^c(j)$ reached by a morphism is the count of $\Lambda_j$ transported along it;
   - off the saturation of $U^c(j)$, $\beta_j = 0$, because $\operatorname{cl}O_j \subset |U^c(j)|$; so $\Lambda_j$ is trivial there.
4. *The classes are equal*, as in step 7 above.

*For a structurable $\Lambda$* ⟦Chapter13/Theorem1357Atomic · SBLocalization.theorem_13_5_7_isAtomic_book⟧: $\Lambda$ has a structured lift $T$ which is the commensurable sum of a locally finite family of atomic pieces, with the same class. *In the form of the text* ⟦Chapter13/Theorem1357Atomic · SBLocalization.theorem_13_5_7_isAtomic_sum⟧: there are common data $c = (\mathcal U, I_x, \tau)$, a structure of $\Lambda$ over $c$, and a locally finite family $(\Lambda_j)_{j \in J}$ over $c$, each atomic, with $\bigoplus^c_j\Lambda_j = \Lambda$ and $\bigoplus^c_j[\Lambda_j, \mathcal U, S_j, \tau] = [\Lambda, \mathcal U, S, \tau]$. In both, the paracompactness of $|X|$ is a hypothesis of the text kept and not used.

### XIII.31 What is not formalized

- No numbered statement of Chapter 13 is open. The chapter's points G.141, G.142, G.143, G.148, G.149 and G.163 are closed:
  - G.141: Theorem 13.1.7 as printed (§XIII.5);
  - G.142: decorated sc⁺-multisections and their algebra (§§XIII.10–XIII.13);
  - G.143: no inverses (§XIII.11);
  - G.148: Proposition 13.3.19 (§XIII.18);
  - G.149: Theorem 13.5.3 and the last clause of Theorem 13.5.5 (§§XIII.26, XIII.28);
  - G.163: Proposition 13.4.2, in the reading of structured data relative to the open $V$ (§XIII.21).
- Remark 13.3.13, the negative half. The claim is that the structured sums $\Lambda_1 \oplus \Lambda_2$ and $\Lambda_2 \oplus \Lambda_1$ differ, because $I^1_x \times I^2_x$ and $I^2_x \times I^1_x$ differ. It is a statement about inequality of types and has no formal counterpart. The positive half, that the two are related by the relabelling, is in §XIII.16.
- Remarks 13.3.9, 13.3.16 and 13.5.2 are prose.
- The text's sub-ep-groupoid $W|V$ in Proposition 13.4.2 is read as data relative to $V$ inside $W$ (§XIII.21). No strong bundle over an open full sub-ep-groupoid is built.

### XIII.32 What the formalization taught us

§13.1 is a study of the bi-action. Once the bi-action is written as a formula, almost everything follows from two facts:
- morphisms between points of a neighbourhood with the natural action are $\Gamma(g, \cdot)$ for a unique $g$;
- $s$ and $t$ are injective on each component.

Lemma 13.1.6 (1) then needs one morphism with $g' * \psi \in \Sigma$, not $g' * \Sigma = \Sigma$. Proposition 13.1.9 follows from Lemma 13.1.6 with the action laws, without the smoothness argument of the text, and with uniqueness among all maps.

The phrase "carries the natural $G_x$-action" needed a decision. Proposition 13.1.3 shrinks to invariant subsets that need not be connected, so a neighbourhood with the natural action cannot be the connected domain of a natural representation. It is an invariant open subset of one. With that reading the section holds as printed.

In Lemma 13.1.1 the two directions use different halves of the hypotheses: properness one way, the natural action the other. The invariance of $V$ is used by neither.

Theorem 13.1.7 holds in two forms.
- With properness read in $X$, it needs neither the openness of $Q$ nor the smallness of the closures of $U(y)$.
- As printed, with properness read in the full subcategory on the open $Q$, the hypothesis is equivalent to properness in $X$ together with $\operatorname{cl}_XU(q) \subset Q$. A limit of points of $U(q)$ outside $Q$ is moved into $Q$ by a local section of $s$, and properness in $Q$ then places it in $Q$.

No sub-ep-groupoid structure is needed: the full subcategory is its set of morphisms, with the restricted source and target.

In §13.2 the multisection algebra is convolution. $\oplus$, scalar multiples and locally finite sums are all sums over decompositions of a vector in a fibre, and their local structures are sums of sections with products of weights. A locally finite sum over infinitely many indices, which the text does not write out, is a sum over finitely supported families. Over $O(x)$ it is a finite convolution.

The decorations add one subtlety. The intersection $U'(x) \cap U''(x)$ of two neighbourhoods with natural actions need not carry one natural action for which both structures are symmetric. So the sum is decorated on a smaller neighbourhood inside it on which the two actions agree, which Definition 13.2.8 allows.

The absence of inverses is a one-line computation once a neutral element is fixed: a two-valued multisection convolved with anything gives weight at most $\tfrac12$ to the zero vector.

§13.3 is mostly combinatorics of finite index sets, and two points needed care.
- The text writes equalities of index sets ($I'_x = \{*\}$, $I'_x = I_x$) where a formalization has bijections. The correspondences are compared after transport along them.
- The tight version of Proposition 13.3.15 needs a compatibility the text does not check. It holds because every section of a structure vanishes where $\Lambda$ is trivial.

Definition 13.3.8 as printed puts no condition on the sections. Nothing proved in this chapter depends on it; Theorem 14.6.3 does, and is formalized with the equality of sections that its proof states on p. 682 (Part XIV, §XIV.28).

Products of infinitely many correspondences are well defined only because, near any two points, all but finitely many factors are the unit diagram $[\{*\} \leftarrow \{*\} \to \{*\}]$. The text's "left to the reader" in Proposition 13.3.19 is this bookkeeping. With the tight versions over a common good system, it is about five hundred lines.

§13.4 is simpler than printed.
- The pull-back needs only $F$ injective on $U(x)$ with $F(U(x)) \subset U'(F(x))$, not the equality the text arranges. The canonicity it asserts is a short argument once the pull-back is written as a map of structured classes.
- The push-forward does not need Proposition 13.4.2. Every point of $X'$, in $F(X)$ or not, gets a chart along a morphism $F(x_y) \to y$, which merges the text's two steps. The lifted morphisms are continuous because $F$ is faithful and a local sc-diffeomorphism.
- Proposition 13.4.2 is then the same chart for the identity equivalence. The text's three cases for the correspondences, with the maps $A$, $C$ and a pseudo-inverse, are one formula: the correspondence of the lifted morphism.
- The commensurable sum of Definition 13.4.5 is well defined because the count is transported along correspondences: $p|I_x| = q|I_{x'}| = |I|$ for the fibre sizes $p$, $q$ of the two legs.

In §13.5 the atomic multisection is determined by its data. The count in Definition 13.5.1 (3) does not depend on the morphism used, and its local structure near any point is the given sections transported by a local inverse of $t$. What the text does not say is that the index set must be nonempty, since the weights of a multisection sum to $1$.

In Theorem 13.5.3 the action of $G_y$ on the index set comes from a single function $H$. It assigns to a morphism the element of $G_{x_0}$ the morphism becomes after both ends are transported into $U(x_0)$. $H$ is functorial, and locally constant because $G_{x_0}$ is finite and $X$ Hausdorff. Every compatibility follows from these two properties. Using the index set $I_{x_0}$ everywhere, with zero sections where $\Lambda$ is trivial and the full correspondence across the frontier of the saturation, avoids the case distinction of the text's $\{*\}$. The theorem needs a good system and nothing else: structurability is equivalent to the existence of one.

Theorem 13.5.7 needs regularity of $|X|$ for its shrinking, which every ep-groupoid has, and partitions of unity, not paracompactness. Its atomic pieces are atomic on neighbourhoods with the natural action, since the sets of a good system need not be connected domains of natural representations.
