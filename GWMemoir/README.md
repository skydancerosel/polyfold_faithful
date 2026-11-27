# The polyfolds of Gromov–Witten theory

Lean formalization of H. Hofer, K. Wysocki, E. Zehnder, *Applications of Polyfold Theory I: The
Polyfolds of Gromov–Witten Theory*, Memoirs AMS 248, no. 1179 (2017) ("the memoir"), built on the
formalization of *Polyfold and Fredholm Theory* (Springer 2021) in [`Polyfold/`](../Polyfold).
It is a separate Lean library (`lake build GWMemoir`); nothing in `Polyfold/` imports it.

Statements carry the memoir's labels (`memoir_theorem_2_46`, `memoir_lemma_5_12`, …) and are proved
from the book's Lean results. Only `propext`, `Classical.choice` and `Quot.sound` are used.

## Contents

| file | memoir | what is proved |
|---|---|---|
| `Recollections.lean` | §2.2, Prop 2.53 | the sc-calculus recollections, as abbreviations of or equivalences with the book's definitions; Lemma 2.35, Props 2.41 and 2.53 as printed |
| `RecollectionsFredholm.lean` | §2.3 | Fredholm germs and sections; Thm 2.46 as printed |
| `PolyfoldStructures.lean` | Defs 2.28–2.38 | polyfold and strong polyfold bundle structures against Defs 16.1.1 and 16.3.1 of the book |
| `FredholmSections.lean` | Ch. 4 | Defs 4.1–4.4, the abstract part of Thm 4.6, Props 4.22, 4.24, 4.26 |
| `Orientation.lean`, `OrientationHomotopy.lean` | App. 5.10 | orientations of sc-Fredholm sections in the memoir's Hilbert-space form: Defs 5.8–5.10, Lemmas 5.11–5.15, Thm 5.16, 5.17–5.26 for X without boundary |
| `Skeleton.lean` | Ch. 1, 3 | the target (Q, ω, J), nodal surfaces and stability (Defs 1.2, 1.3), stable maps (Def 1.4), the sc-scale of the model spaces; Thms 3.13 and 3.22 as named statements; Thm 3.22 gives a metrizable orbit space |
| `Groupoid.lean` | §3.1 | the groupoid of stable maps and their isomorphisms, as the groupoidal category of Definition 19.1.1 of the book |
| `Witnesses.lean` | Defs 1.1–1.4 | the sphere with its standard complex structure and holomorphic stereographic charts; the sphere with three marked points and the sphere with one node; constant stable maps into any target |
| `Reductions.lean`, `ReductionsRegularity.lean` | Thm 3.13, §3.5 | transition data from Thm 3.13; (ZHOU), effectiveness and tameness for faithful linear actions; Z is metrizable with (ZHOU) and carries a polyfold structure, given Prop 3.10, Thms 1.6, 3.13, 3.22 as named statements |
| `FilledSection.lean`, `FredholmGerm.lean` | Props 4.7–4.8 | Prop 4.8 from Props 4.7, 4.23 and 4.25, through Prop 4.26; Prop 4.8 gives the sc-Fredholm germ property (Def 3.1.11 of the book) |
| `SphereStability.lean` | Def 1.3 | the sphere with three marked points is stable: every automorphism is the identity (Liouville in a stereographic chart) |
| `NodalPair.lean` | Defs 1.2–1.4 | two spheres joined at a node, with four marked points, and a constant stable map on it; charts and tangent coordinates of disjoint unions of manifolds |
| `HalfCylinders.lean` | §2.4 | weighted Sobolev spaces on half-cylinders and finite cylinders as restrictions of the cylinder spaces of `Polyfold/Chapter1`, and their sc-structure |
| `Scales.lean` | §2.4 | the scales H^{ℓ+m,δ_m} for every offset ℓ; Thm 2.50 (1): hat gluing for fixed a is an sc-isomorphism (Thm 2.50 (2) stated) |
| `SectionSpaces.lean` | §3.1 | the section spaces H^{3,δ₀}_c(S, u*TQ) and E_u inside a finite product of disc and neck pieces, the neck pieces in holomorphic polar coordinates (Def 1.1) |
| `LocalAddition.lean` | Def 3.6 | the exponential map read as a local addition affine in the charts; that the geodesic exponential is one is stated |
| `CauchyRiemann.lean`, `CauchyRiemannSection.lean` | §4.2 | ∂̄_J on stable maps, its naturality under isomorphisms, and the section functor it defines |
| `Bundle.lean` | Prop 3.39, Thm 1.10 | the strong polyfold bundle W → Z from the named Prop 3.39 |
| `CauchyRiemannFredholm.lean` | Thm 1.11 | from the named Props 4.7, 4.23, 4.25: ∂̄_J is an sc-Fredholm section with tame germs, its solution set the classes of J-holomorphic stable maps |
| `Fibres.lean`, `FibreRepresentation.lean`, `FibreInstance.lean` | §1.2 | the fibres of W: forms of class (2+m, δ_m) inside a finite product over an atlas (completeness and density stated); ∂̄_J of a constant map is 0; the fibre representation and its instances |
| `Evaluation.lean`, `EvaluationForms.lean` | Thm 1.12 | finite-dimensional manifolds and their products as polyfolds, smooth forms as sc-forms (closed to closed), ev : Z → Q^m (its sc-smoothness on uniformizers stated), and Thm 1.12 for closed forms on Q^m |
| `ConstantBase.lean`, `ConstantInstance.lean` | Thms 1.10, 1.11 | on the constant maps from the three-pointed sphere: the uniformizer construction, with Prop 3.10, Thms 1.6, 3.13, 3.22 proved, the polyfold structure on Z ≅ Q, and Thms 1.10 and 1.11 with the base and fibre hypotheses discharged |
| `ConstantBundle.lean`, `PullbackBounded.lean` | Thm 1.10 | the vector bundle (Def 17.7.1 of the book) over the constant maps from the three-pointed sphere, read in one atlas; the change-of-atlas bound reduced to a bounded operator on the block spaces |
| `Completeness.lean`, `CompletenessForms.lean` | §§1.2, 3.1 | the embedding H^{2,δ}(ℝ × S¹) ⊂ C⁰; completeness of the section and constraint spaces for surfaces without nodes and of the fibres of W in general; density reduced to density of the smooth points on every level |
| `ChartChange.lean`, `ChartChangeInstances.lean`, `ChartChangeDensity.lean` | §§1.2, 3.1 | v ↦ a·(v∘ψ) is bounded on H^{k,δ} for every k and commutes with the inclusions; with it, the change-of-atlas bound and density of smooth sections for constant maps on surfaces without nodes, in particular the three-pointed sphere |
| `CompletenessNodes.lean`, `SectionAtlasNodes.lean` | §3.1 | completeness of the section and constraint spaces with nodes, for every continuous map and atlas; every stable map has an atlas (instance: the sphere with one node) |
| `FormsDensity.lean` | §1.2 | the matrix of j in a disc chart is smooth; density of smooth forms for constant maps on surfaces without nodes, in particular the three-pointed sphere |
| `LinearCR.lean`, `LinearCRKernel.lean`, `LinearCRSphere.lean`, `LinearCRFredholm.lean` | §§4.3, 5.3 | the linearization of ∂̄_J at a constant map from the three-pointed sphere with constant J: a bounded operator from the section space to the fibre; its kernel is the constants (Liouville), and 0 with the constraints at the three marked points; with the elliptic estimate it has closed range, and with the vanishing of the cokernel it is Fredholm of index 2n |
| `CauchyTransform.lean`, `CokernelSphere.lean`, `CokernelSphereDense.lean`, `EllipticEstimate.lean`, `EllipticEstimateSphere.lean`, `LinearCRSphereFredholm.lean` | §4, App. 5.3 | at a constant map from the three-pointed sphere: ∂̄ξ = η solved on the Riemann sphere (Cauchy transform in each chart, glued), the range of D dense, the elliptic estimate ‖ξ‖_{H³} ≤ C(‖Dξ‖_{H²} + ‖ξ‖_{L²}); so D is Fredholm and onto, of index dim E, with no named proposition |
| `ConstraintIndex.lean` | Def 3.6, Thm 4.6 | with constraints ξ(z_l) ∈ H_l at distinct points, D is Fredholm of index dim E − Σ codim H_l; ξ = 0 at the three marked points gives index −2 dim E. The memoir's constraints sit at a stabilization set Σ whose points each complement the image of Tu(z) (Def 3.6 (4), (7)); at a constant map Tu(z) = 0, so Σ = ∅ and the index is dim E, as in Thm 4.6 at genus 0 with A = 0 |
| `LinearModel.lean`, `LinearModelFredholm.lean` | Props 4.7, 4.8, 4.23, 4.25 | for a section of the local bundle given by a linear sc-operator T: Prop 4.25 always, Prop 4.7 when T is regularizing, Props 4.23 and 4.8 when T is sc-Fredholm. Instance: at a constant map from the three-pointed sphere into a linear target with constant J, ∂̄_J(q+ξ) = Dξ on the base H^{3,δ₀}, D is an sc-operator on the levels H^{3+n,δ_n} → H^{2+n,δ_n}, Fredholm on level 0, and Prop 4.25 holds; given elliptic regularity from each level to the next (`LevelRegularity`, named), D is sc-Fredholm, Props 4.7, 4.23, 4.8 hold and ∂̄_J is an sc-Fredholm germ at u. The data exist on ℝ² with its standard J |
| `LevelRegularityEstimate.lean`, `LevelRegularityDense.lean`, `LevelRegularitySphere.lean` | Props 4.7, 4.8, 4.23 | at the same constant map: the elliptic estimate and dense range on every level, so D is onto H^{3+m,δ_m} → H^{2+m,δ_m} for each m and `LevelRegularity` holds (for 0 < δ₀); hence D is sc-Fredholm, Props 4.7, 4.23, 4.8 hold and ∂̄_J is an sc-Fredholm germ at u, with no named proposition |
| `NeckEstimate.lean` | §4.3, Prop 4.15 | on the cylinder ℝ × S¹ with weight δ, for 0 < δ < 2π and J² = −1: ‖r‖_{H^{m+1,δ}} ≤ C‖(∂_s + J∂_t) r‖_{H^{m,δ}} on n-tuples, for every m, with no lower-order term; also for tuples vanishing for s ≤ 0. The constant comes from the gap min(δ, 2π − δ) on circles; instance δ = π |
| `CokernelNodesNeck.lean`, `CokernelNodes.lean` | §3.1 p. 66, §4 | at a constant map from two spheres joined at a node: a section smooth near the node lies in H^{3,δ₀}_c for 0 ≤ δ₀ < 2π, by the decay O(e^{−2πs}) in the polar chart; ∂̄ξ = η is solvable in H^{3,δ₀}_c, one sphere at a time with the constants matched at the node. For δ₀ ≥ 2π the smooth section c + χ·z·e has no representative in the blocks |
| `LinearCRNodes.lean`, `LinearCRNodesKernel.lean`, `LinearCRNodesOp.lean`, `LinearCRNodesOpNeck.lean`, `GlueDataNodes.lean` | Prop 4.23 at a = 0 | at a constant map from two spheres joined at a node: a section whose ∂̄-form has representative 0 is holomorphic off the node on each sphere, hence constant, and matching at the node gives one constant, so the kernel is E. With gluing data `GlueDataN` (a partition of unity over the disc and neck charts with the chart changes between them), `LinearCRNodesOp.lean` and `LinearCRNodesOpNeck.lean` build the bounded operator D with its neck rows ½(∂_s + J∂_t), show that it represents ∂̄ on the polar charts, and give ker D ≅ E. `GlueDataNodes.lean`: such gluing data exist on an atlas whose node map is injective and whose closed discs miss the nodes (`exists_glueDataN`), so ker D ≅ E holds with no hypothesis (`exists_linCRN_ker_equiv`) |
| `Invariants.lean` | Thm 1.12 | with Gromov compactness, the index and an orientation (named), an admissible perturbation exists and ∫ ev*τ over its solution set depends neither on the perturbation nor on τ up to an exact form |
| `Gluing.lean`, `GluingLemma248.lean`, `GluingSplicing.lean`, `NeckOperators.lean`, `GluingLevels.lean`, `GluingIso.lean` | §2.4 | gluing, anti-gluing and hat gluing; Lemma 2.48 and (2.6)–(2.12); Thm 2.49 (1): for fixed a, the total gluing map is an sc-isomorphism on every level; the projections π_a; Prop 2.51 |

## Readings and comparisons with the book

- **Thm 2.46.** The book's Theorem 3.1.22 assumes d_X ≡ 0; the memoir does not. The memoir's basic
  germs (Def 2.43) have no quadrant factor, and the conjugating isomorphism keeps the degeneracy index
  at 0, so every point carrying a Fredholm germ has d_X = 0: the theorem holds as printed.
- **Def 2.44.** The filler is taken after subtracting the sc⁺-germ (Def 3.1.11 of the book: before). A
  memoir germ is a tame germ of the book (through Prop 2.42).
- **Def 2.22.** Read literally, condition (2) gives tameness condition (2) of Def 2.5.2; for C = E the
  local models are the sc-retracts.
- **Defs 2.29 and 2.38.** The memoir's structures do not ask for (ZHOU) or the local regularity of Def
  8.4.2. Paracompactness of the orbit space follows from that of Z; (ZHOU) does not follow (ℤˣ acting on
  the space of Appendix 7.6.3 of the book). Equivalence through a third structure agrees with the book's
  generalized isomorphisms.
- **Def 2.37 (3).** The side condition s(t) = p(e) is read as s(g) = p(e), under which μ(g, e) is defined.
- **Def 4.4.** "Proper" (compact solution set) agrees with Def 16.6.3 for Fredholm sections (Thm 16.6.4).
- **Prop 4.26.** In (3), x is taken on level m+1 and small on level m, as in Thm 3.7.1 of the book.
- **Lemma 5.12.** With orthogonal projections, as in the memoir, the common lower bound exists; with
  the book's bounded projections (Lemma 6.4.9) it need not.
- **Def 5.9.** The memoir's construction with D* and d*∘γ corresponds to the book's (6.4) under ι.
- **Lemma 5.24.** For X without boundary it follows from Thm 6.6.13 of the book, with tame germ data
  for f and bump functions.
- **Thm 3.13 ⇒ transition data.** The reduction uses two properties of the uniformizers, which the
  construction of §3 is to supply: the core-smoothness class is closed under the group action, inverses
  and composition, and each object maps to finitely many uniformizers (the locally finite refinement of
  §3.5). Prop 3.10, the existence of good uniformizers at every object, is a hypothesis of the final
  statement: without it the conclusions of Thms 3.13 and 3.22 would hold for an empty family.
- **Gluing (§2.4).** The spaces on half-cylinders and on the finite cylinders Z_a are taken as
  restrictions of the cylinder spaces; the equivalence with the intrinsic norms is not formalized. The
  gluing parameters range over B_{1/2}, and only R ≥ 2 is used. The average [h]_R is read as the trace
  ∫_{S¹} h(R, t) dt. In the display before (2.11), the shifted term h⁻(s − R, t − R) is read with second
  argument t − ϑ. Prop 2.51 is read in a chart flat on ‖ψ‖ < 2.
- **Thm 2.50.** The domain printed as E is read as F.
- **The exponential map (Def 3.6).** Read as a local addition affine in the charts ψ_w, a wider class
  than geodesic exponentials; as we read the proof of Thm 3.13, the exponential map enters only through
  properties this reading keeps.
- **Components (Thm 1.12).** A component is a full subcategory of stable maps closed under isomorphism;
  a class A enters through its energy ω(A).
- **Fibres of W.** A fibre element of W is a form along u, and the Banach fibre sees it through its
  local representatives. A form that is nonzero at a single point has zero representatives, so the
  fibre map is injective only on continuous forms (`not_factor_of_injOn_fibreElements`);
  `FibreRepresentation` asks for exactly that, and Thm 1.11 uses that ∂̄_J u is continuous.
- **How Thms 1.10–1.12 are reached.** The bundle W → Z is taken in the form of Chapter 17.7 of the book
  (Prop 3.39 stated there). The fibre hypotheses of Thm 1.11 hold on the constant maps from the sphere
  with three marked points with no named proposition (`memoir_theorem_1_11_fibre_nonvacuous`), and on
  stable maps without nodes given the change-of-coordinates bound `AllPullbackBounded`. On the constant
  maps from that sphere the uniformizer construction (Def 19.1.3 of the book) is built and every named
  proposition of the base is proved (`ConstantBase.lean`). That piece has no nodes and no gluing, so it
  checks how the statements fit together, not the memoir's analysis; and Props 4.7, 4.23, 4.25 have no
  instance on it as we read them, because its base is finite-dimensional while the fibres are not. They
  have one on the base H^{3,δ₀} at a constant map into a linear target (`LinearModelFredholm.lean`,
  `LevelRegularitySphere.lean`), with no named proposition; there is no gluing and no moduli of the
  domain in that case. For
  the GW data near nonconstant maps, the uniformizer construction and the vector bundle structure (Def
  17.7.1) are not yet instantiated; Thms 1.10–1.12 are proved for every instance of them.
- **The weights.** The bound 0 < δ_m < 2π, printed on p. 49 "for all m ≥ 1", is read for m ≥ 0, as on
  pp. 58 and 104: for δ₀ ≥ 2π a smooth section near a node is not of class (3, δ₀)
  (`not_mem_sectionSpace_of_two_pi_le`).

## Not yet formalized

The analysis and geometry the memoir draws on beyond the book: Deligne–Mumford spaces, weighted Sobolev
the sc-smoothness of gluing and anti-gluing in the gluing parameter (Thm 2.49 (2), stated as a named
proposition; Thms 2.50, 2.55, 2.57), elliptic regularity for ∂̄_J, the index theorem, Gromov compactness, and the
results resting on them (Thms 1.6–1.12, 3.13, 3.22, Props 3.10, 4.7, 4.23, 4.25, stated here as named
propositions). Also the section spaces H^{3,δ₀}_c(S, u*TQ), Lemma 5.20 beyond a single chart, Defs 5.25 and
5.27–5.32, and the abstract parts of Appendix 5.11 after Lemma 5.37.
