import Polyfold.Chapter9.Symmetric
import Polyfold.Chapter4.Families
import Polyfold.Chapter6.OrientableNbhd

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.1 "Basic Definitions": the local dimension of a submanifold
(**Remark 9.1.1**, p. 402; 2017: Remark 9.1, p. 291), `n`-dimensional branched ep⁺-subgroupoids
(the last paragraph of **Definition 9.1.2** with its footnote, p. 402; 2017: after Definition 9.1,
p. 292, without the footnote), **Remark 9.1.3 (b)** (p. 403; 2017: Remark 9.2 (b), p. 292),
**Proposition 9.1.11** (pp. 407–408; 2017: Proposition 9.2, p. 297) and **Proposition 9.1.12**
(p. 408, proof in §9.6.1, pp. 452–457; new in 2021, the 2017 proof of Proposition 9.2 calls the
uniqueness obvious).  Numbers and pages are the 2021 text's, the 2017 ones in parentheses.
Proposition 9.1.9 is not treated here.

# The dimensional decomposition of a branched ep⁺-subgroupoid

## The text, paraphrased

(Remark 9.1.1, p. 402) The dimension of `T_mM` is locally constant in `m ∈ M`; it is the local
dimension of the submanifold `M`.

(Definition 9.1.2, last paragraph, p. 402) `Θ` is `n`-dimensional if at every `x ∈ supp(Θ)` the
manifolds of a local branching structure can be taken `n`-dimensional (2017: are all
`n`-dimensional); by the footnote, an `n`-dimensional `Θ` is not `m`-dimensional for `m ≠ n`.

(Remark 9.1.3 (b), p. 403) Local branching structures are not unique, even near `x`.  On
`X = ℝ²` with only identity morphisms take smooth `β₁, β₂ : ℝ → ℝ` with `β₁ = 0` on `s ≤ 0`,
`β₁ > 0` on `s > 0`, `β₂ > 0` on `s < 0`, `β₂ = 0` on `s ≥ 0`, their graphs `G₁`, `G₂` with weight
`1`, and `Θ(p) = #{i | p ∈ Gᵢ}`.  The graphs of `γ₁ = 0` and of a `γ₂` with `γ₂(s) > 0` for
`s ≠ 0` give another branching structure describing `Θ`.

(Proposition 9.1.11, pp. 407–408) A branched ep⁺-subgroupoid `Θ` has a unique sequence
`Θ_0, Θ_1, …` of branched ep⁺-subgroupoids characterized by (1) `Θ_k` is `k`-dimensional and
(2) `Θ = Θ_0 + Θ_1 + ⋯`; the sum is locally finite.  Proof: `Θ_k = 0` off `supp(Θ)`; at
`x ∈ supp(Θ)` take a symmetric local branching structure on `U(x)`, split `I = I_0 ⊔ ⋯ ⊔ I_n`
by the dimension of the `Mᵢ` (the `I_k` are `G_x`-invariant since `G_x` preserves dimension) and
put `Θ_k(y) = ∑_{i ∈ I_k, y ∈ Mᵢ} σᵢ`.  That this does not depend on the local branching
structure is Proposition 9.1.12.

(Proposition 9.1.12, p. 408) For two local branching structures of `Θ` on `U(x)` there is an open
`G_x`-invariant `V(x) ⊆ U(x)` (with the usual properties) on which the two dimensional
decompositions agree.  The proof (§9.6.1) shows that the top dimensions agree (Lemma 9.6.1) and
that the union `M_U^k` of the top-dimensional `Mᵢ` does not depend on the structure (Lemma 9.6.2),
both by a "measure zero" argument; it defines top-good and top-bad points (Definition 9.6.3),
shows that they do not depend on the structure (Lemma 9.6.4), and at a top-bad `x` writes
`Θ_k(x)` through top-good points near `x`, using the classes of the `T_xMᵢ` (Proposition 9.6.5,
modelled on Proposition 9.2.8); then it descends to the lower dimensions.

## What is formalized

* **Dimension of a submanifold** (Remark 9.1.1, with Definition 4.13 [4.4] and Remark 4.14):
  `MPolyfold.HasDimAt` (`dim T_aA = k`, in a chart), its chart independence
  `finrank_tangentSpace_chart_change`, `HasDimAt.finrank_eq'`, `HasDimAt.finrank_eq` (from
  `finrank_span_tangentSpace_eq`: a germ of sc-diffeomorphisms restricts to an isomorphism of
  tangent spaces of sub-retracts), `HasDimAt.unique`, `IsSmoothSubmanifold.exists_hasDimAt`,
  `hasDimAt_inter_isOpen_iff`, `hasDimAt_image_iff` (invariance under sc-diffeomorphisms);
  `MPolyfold.IsSubmanifoldOfDim` (`n`-dimensional submanifold) with `inter_isOpen`,
  `image_of_isScDiffeoOn`, `eq_of_hasDimAt`.
* **Submanifolds of `ℝⁿ`**: the image of a smooth idempotent `s : ℝⁿ → ℝⁿ` is a closed smooth
  submanifold (`rnPolyfold_isScPlusRetractionOn_univ`, `rnPolyfold_isSmoothSubmanifold_range`,
  `isClosed_range_of_idem'`) of dimension `rank Ds(a)` (`rnPolyfold_hasDimAt_range`); graphs
  `graph2 β` in `ℝ²` as images of `(s, t) ↦ (s, β(s))` (`graphRetraction`) are closed
  `1`-dimensional submanifolds (`rnPolyfold_isSubmanifoldOfDim_graph2`, `isClosed_graph2`); points
  are `0`-dimensional (`rnPolyfold_isSubmanifoldOfDim_singleton`).
* **`n`-dimensional `Θ`** (Definition 9.1.2): `LocalBranchingStructure.IsOfDim`,
  `EpGroupoid.IsNDimensional`, `isNDimensional_zero`.
* **The local construction of Proposition 9.1.11**: `LocalBranchingStructure.dim_unique` (the
  dimensions of the `Mᵢ` are determined), `dimPart` (`Θ_k` on `U(x)`), `dimPartStructure` and
  `dimPartStructure_isOfDim` (`Θ_k` has the `k`-dimensional local branching structure
  `(Mᵢ)_{i ∈ I_k}`), `eq_sum_dimPart` (`Θ = ∑_k Θ_k` on `U(x)`), `dimPart_eq_zero`,
  `dimPart_eq_of_isOfDim`; for a symmetric structure (Lemma 9.1.7)
  `SymmetricBranchingStructure.dim_smul` (`G_x` preserves dimension) and `dimPart_Φ` (`Θ_k` is
  `G_x`-invariant on `U(x)`).
* **Proposition 9.1.11, the statement** `EpGroupoid.Proposition_9_1_11` (with
  `IsDimDecomposition`, `IsLocallyFiniteFamily`), and `not_proposition_9_1_11_rn`: as we read it,
  the uniqueness does not hold (below).
* **Proposition 9.1.12, the statement** `EpGroupoid.Proposition_9_1_12` (with
  `LocalBranchingStructure.DimPartsAgreeNear` and `DimPartsAgreeNear.exists_naturalRep`), and its
  equidimensional case `dimPartsAgreeNear_of_isOfDim`.  The general case is not proved (below).
* **Branched ep⁺-subgroupoids of the trivial ep-groupoid of `ℝⁿ`**:
  `paracompactSpace_orbitSupp_trivial_rn`, `localBranchingStructure_sum_rn`,
  `isBranchedEpSubgroupoid_sum_rn`, `isNDimensional_sum_rn` (finite weighted sums of closed
  submanifolds), `localBranchingStructure_indicator_rn`, `isBranchedEpSubgroupoid_indicator_rn`
  (indicators of locally closed submanifolds).
* **Remark 9.1.3 (b)**: `remark_9_1_3_b` under `Remark913Hyp` (satisfiable:
  `remark913Hyp_expNegInvGlue`), with `thetaGraphs`, `thetaGraphs_eq`,
  `Remark913Hyp.structureβ`, `Remark913Hyp.structureγ`, `Remark913Hyp.γ₂_pos` and
  `Remark913Hyp.eq_add_of_thetaGraphs_eq`.

## Proposition 9.1.11: the uniqueness does not hold as we read it

On the trivial ep-groupoid of `ℝ²` (the setting of Remark 9.1.3 (b)) let `L` be the `x`-axis and
`Θ = 1_L`.  Both `Θ_0 = 1_{0}`, `Θ_1 = 1_{L ∖ {0}}` and `Θ_0 = 0`, `Θ_1 = 1_L` (all other
`Θ_k = 0`) satisfy (1) and (2): `L ∖ {0}` is a `1`-dimensional submanifold properly embedded in
the open set `ℝ² ∖ {0}`, which is all Definition 9.1.2 asks at its points
(`decompA_isDimDecomposition`, `decompB_isDimDecomposition`, `not_proposition_9_1_11_rn`).  So (1)
and (2) do not characterize the sequence.  What the proof establishes, granted Proposition 9.1.12,
is that the decomposition built from local branching structures of `Θ` is well defined; that
decomposition is the second one.  An extra condition singling it out, for instance that every
`Θ_k` be represented near each `x ∈ supp(Θ)` by a subfamily of a local branching structure of `Θ`
(or that `supp(Θ_k)` be closed in `supp(Θ)`, which fails for `L ∖ {0}`), is a possible repair;
it and the reduction of the uniqueness to Proposition 9.1.12 are not formalized.

## What the text leaves implicit, and the choices made

* "The dimension of `T_aA`": the project's Part I does not make `T_aX` a vector space (gap G.7),
  so `HasDimAt` measures the tangent space `T_z(φ(W ∩ A))` of the sub-retract in a chart, as
  Remark 4.14 does.  It asks for *some* data and chart; `HasDimAt.finrank_eq` proves the value is
  the same for *every* data and chart, so no "for all charts" hypothesis is needed; it is
  satisfied by graphs and points (`rnPolyfold_isSubmanifoldOfDim_graph2`, `..._singleton`).
* Local constancy (Remark 9.1.1) is not proved, so a submanifold may a priori have several
  dimensions.  The splitting `I = I_0 ⊔ ⋯ ⊔ I_n` presupposes that each `Mᵢ` has one dimension;
  we take labellings `dim : I → ℕ` with `IsSubmanifoldOfDim (Mᵢ) (dim i)` as hypotheses.  Since
  all `Mᵢ` pass through `x`, such a labelling is unique (`dim_unique`).
* "`Θ` is `n`-dimensional": there is, at each `x ∈ supp(Θ)`, a local branching structure all of
  whose `Mᵢ` are `n`-dimensional (the 2021 "can be taken as").  The zero functor is
  `n`-dimensional for every `n`; the footnote concerns `Θ ≠ 0`.
* (2) `Θ = Θ_0 + Θ_1 + ⋯` is read pointwise: at each object only finitely many `Θ_k` are nonzero
  and `Θ` is their `finsum`.  Local finiteness is a separate conclusion (`IsLocallyFiniteFamily`).
  "Uniquely determined … uniquely characterized" is `∃!` of the family `(Θ_k)`.
* Proposition 9.1.12's `V(x)` "open, `G_x`-invariant, with the usual properties": any open
  `V ∋ x` inside both domains; `DimPartsAgreeNear.exists_naturalRep` shrinks it to the domain of a
  natural representation of `G_x` (Theorem 7.1), so the two readings agree.  The decomposition of
  a structure is taken on its own domain, which contains the restricted one on `V`.
* Remark 9.1.3 (b): `#{i | p ∈ Gᵢ}` is the sum of the weights `1` (`thetaGraphs_eq_card`).  The
  text gives `γ₂` only through `γ₂(s) > 0` for `s ≠ 0`; describing the same `Θ` forces
  `γ₂ = β₁ + β₂` (`eq_add_of_thetaGraphs_eq`), which is smooth and positive off `0`
  (`γ₂_pos`).  The graphs are submanifolds as images of the sc⁺-retraction
  `(s, t) ↦ (s, β(s))` of `ℝ²`, closed, hence properly embedded (`isProperMap_inclusion_iff`).
  "Not unique, even close to `x`" is read as: no submanifold of the one structure agrees with a
  submanifold of the other on any neighbourhood of the origin (the last conjunct of
  `remark_9_1_3_b`).

## Not formalized, and why

* **The proof of Proposition 9.1.12** beyond the equidimensional case.  It needs (a) the
  "measure zero" and "moving `z` slightly" steps of Lemmas 9.6.1, 9.6.2, 9.6.4: a nonempty open
  piece of a `k`-dimensional submanifold is not covered by finitely many submanifolds of smaller
  dimension, nor by finitely many closed `k`-dimensional ones not containing it near the point.
  Part I has no measure or dimension theory for submanifolds of an M-polyfold, and the graph
  representation of Proposition 4.9 needs good position; (b) Proposition 9.6.5, which rests on
  the good-point analysis of §9.2 (Proposition 9.2.8) and on the classes of the `T_xMᵢ` as
  linear subspaces of `T_xX`; (c) the local constancy of the dimension (Remark 9.1.1).
* **The global part of Proposition 9.1.11**: gluing the local `Θ_k` into functors on `X`
  (compatibility across morphisms between different objects, paracompactness of
  `|supp(Θ_k)|`, local finiteness).  It rests on Proposition 9.1.12 and, for uniqueness, on an
  extra condition as above.
* The footnote to Definition 9.1.2 (an `n`-dimensional `Θ ≠ 0` is not `m`-dimensional), the
  notion "locally equidimensional", and Proposition 9.1.9.

## Possible misprints (§9.6.1)

* Proposition 9.6.5 (1), p. 456: the `I^e` are subsets of `Ξ`, so "`I_k = I¹ ⊔ ⋯ ⊔ I^p`" reads
  as `Ξ = I¹ ⊔ ⋯ ⊔ I^p`; with that, the formula on p. 457 holds.
* The formula `Θ_k(x) = ∑_Ξ ∑_e Θ_k(x_e^k)` on p. 457: the points `x_e^k` are not introduced;
  presumably a point `x_j^e` of the sequences of Proposition 9.6.5 (2) (any `j`).
* "This completes the proof of Proposition 9.6.5" (p. 457): Proposition 9.6.5 is stated without
  proof; presumably the proof of Proposition 9.1.12 is meant.
* Proof of Lemma 9.6.4 (p. 455): the top-good point is called `z` and then `y` ("move `y` to a
  point `y₁`", "`y` will also be top-good"); presumably the same point.
-/

set_option maxSynthPendingDepth 3

open Set Module Submodule Filter Topology

noncomputable section

namespace Polyfold

/-! ### The dimension of a smooth finite-dimensional submanifold -/

section TangentDim

variable {E E' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)}

/-- The tangent space of a retract at a level-`1` point is a linear subspace: it equals its span. -/
theorem coe_span_tangentSpace {Q : Set (E 0)} (hQ : IsScRetract E C Q) {z : E 1}
    (hz : z ∈ E.lvlSet Q 1) :
    (span ℝ (tangentSpace E C Q z) : Set (E 0)) = tangentSpace E C Q z := by
  obtain ⟨S, rfl⟩ := hQ
  rw [tangentSpace_eq_coe_submodule S hz, span_eq]

/-- **The dimension of the tangent space of a sub-retract is carried by a germ of
sc-diffeomorphisms**: in the situation of `IsGoodPositionRetractAt.transport`, the derivative
`D(F ∘ r)(z)` restricts to a linear isomorphism `T_zQ ≅ T_{F(z)}Q'` (inverse `D(G ∘ r')(F(z))`),
so the two tangent spaces have the same `finrank`. -/
theorem finrank_span_tangentSpace_eq {R : ScRetraction E C} {R' : ScRetraction E' C'}
    {F : E 0 → E' 0} {G : E' 0 → E 0} (h : R.IsDiffeoGerm R' F G)
    (hFs : IsScSmooth R.U (F ∘ R)) (hGs : IsScSmooth R'.U (G ∘ R'))
    {Q : Set (E 0)} {Q' : Set (E' 0)} (hQ : IsScRetract E C Q) (hQ' : IsScRetract E' C' Q')
    (hQR : Q ⊆ R.retract) (hQ'R : Q' ⊆ R'.retract) (hFQ : MapsTo F Q Q') (hGQ : MapsTo G Q' Q)
    {z : E 1} (hz : z ∈ E.lvlSet Q 1) :
    finrank ℝ (span ℝ (tangentSpace E C Q z)) =
      finrank ℝ (span ℝ (tangentSpace E' C' Q' (levelMap (F ∘ R) 1 z))) := by
  have hx : z ∈ E.lvlSet R.retract 1 := hQR hz
  have hy' : levelMap (F ∘ R) 1 z ∈ E'.lvlSet R'.retract 1 := h.image_mem hx
  have hzQ' : levelMap (F ∘ R) 1 z ∈ E'.lvlSet Q' 1 := by
    rw [ScBanach.mem_lvlSet, h.toBase_image hx]; exact hFQ hz
  have himg : levelMap (G ∘ R') 1 (levelMap (F ∘ R) 1 z) = z := h.image_image hx
  have hT := coe_span_tangentSpace hQ hz
  have hT' := coe_span_tangentSpace hQ' hzQ'
  have ha : ∀ v ∈ span ℝ (tangentSpace E C Q z),
      scDeriv R.U (F ∘ R) z v ∈ span ℝ (tangentSpace E' C' Q' (levelMap (F ∘ R) 1 z)) := by
    intro v hv
    rw [← SetLike.mem_coe, hT] at hv
    rw [← SetLike.mem_coe, hT']
    exact scDeriv_mem_tangentSpace_of_subset R hFs hQ hQ' hQR hFQ hz hv
  have ha' : ∀ w ∈ span ℝ (tangentSpace E' C' Q' (levelMap (F ∘ R) 1 z)),
      scDeriv R'.U (G ∘ R') (levelMap (F ∘ R) 1 z) w ∈ span ℝ (tangentSpace E C Q z) := by
    intro w hw
    rw [← SetLike.mem_coe, hT'] at hw
    rw [← SetLike.mem_coe, hT]
    have := scDeriv_mem_tangentSpace_of_subset R' hGs hQ' hQ hQ'R hGQ hzQ' hw
    rwa [himg] at this
  have h1 : ∀ v ∈ span ℝ (tangentSpace E C Q z),
      scDeriv R'.U (G ∘ R') (levelMap (F ∘ R) 1 z) (scDeriv R.U (F ∘ R) z v) = v := by
    intro v hv
    rw [← SetLike.mem_coe, hT] at hv
    have hv' := tangentSpace_subset_of_subset R hQ hQR hz hv
    rw [tangentSpace_eq_range R hx] at hv'
    obtain ⟨w, rfl⟩ := hv'
    rw [h.deriv_inv_deriv hx]
    exact congrArg (fun L : E 0 →L[ℝ] E 0 => L w) (R.scDeriv_comp_self hx)
  have h2 : ∀ w ∈ span ℝ (tangentSpace E' C' Q' (levelMap (F ∘ R) 1 z)),
      scDeriv R.U (F ∘ R) z (scDeriv R'.U (G ∘ R') (levelMap (F ∘ R) 1 z) w) = w := by
    intro w hw
    rw [← SetLike.mem_coe, hT'] at hw
    have hw' := tangentSpace_subset_of_subset R' hQ' hQ'R hzQ' hw
    rw [tangentSpace_eq_range R' hy'] at hw'
    obtain ⟨u, rfl⟩ := hw'
    rw [h.deriv_deriv_inv hx]
    exact congrArg (fun L : E' 0 →L[ℝ] E' 0 => L u) (R'.scDeriv_comp_self hy')
  exact (restrictEquiv _ _ _ _ ha ha' h1 h2).toLinearEquiv.finrank_eq

end TangentDim

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

variable (P : MPolyfold X) in
/-- **The dimension of a smooth finite-dimensional submanifold at a point** (Remark 9.1.1: "the
dimension of `T_mM`"): `A` has dimension `k` at `a ∈ A` if, for some data `d` of Definition 4.13
at `a`, some chart `φ` of `X` at `a` and the level-`1` point `z` over `φ(a)`, the tangent space
`T_aA = T_z(φ(W ∩ A))` (Remark 4.14) has dimension `k`.  `T_aX` carries no linear structure in
Part I (gap G.7), so the condition is stated in a chart, as Definition 4.16 is; it then holds for
all charts (`HasDimAt.finrank_eq`), and `k` is unique (`HasDimAt.unique`). -/
def HasDimAt (A : Set X) (a : X) (k : ℕ) : Prop :=
  a ∈ A ∧ ∃ (d : P.SubmanifoldData A) (φ : MChart X) (z : φ.model.E 1),
    a ∈ d.V ∧ P.IsChart φ ∧ a ∈ φ.source ∧ φ.model.E.toBase 1 z = φ a ∧
    finrank ℝ (span ℝ (tangentSpace φ.model.E φ.model.C (φ '' (d.toSubData.shrink φ ∩ A)) z)) = k

variable {P : MPolyfold X}

/-- **The chart change for the dimension of the tangent spaces of `A`**: for charts `φ`, `φ'` of
`X`, open `G ⊆ dom φ`, `G' ⊆ dom φ'` with `φ(G ∩ A)`, `φ'(G' ∩ A)` retracts, a smooth point
`a ∈ A ∩ G ∩ G'` and level-`1` points `z`, `z'` over `φ(a)`, `φ'(a)`, the tangent spaces
`T_z(φ(G ∩ A))` and `T_{z'}(φ'(G' ∩ A))` have the same dimension (`chart_change_of_transport`
for the property "`finrank T_zQ = k`", with `finrank_span_tangentSpace_eq`). -/
theorem finrank_tangentSpace_chart_change {P : MPolyfold X} {φ φ' : MChart X} (hφ : P.IsChart φ)
    (hφ' : P.IsChart φ') {A G G' : Set X} (hG : IsOpen G) (hG' : IsOpen G')
    (hGφ : G ⊆ φ.source) (hGφ' : G' ⊆ φ'.source)
    (hQ : IsScRetract φ.model.E φ.model.C (φ '' (G ∩ A)))
    (hQ' : IsScRetract φ'.model.E φ'.model.C (φ' '' (G' ∩ A))) {a : X} (haA : a ∈ A)
    (haG : a ∈ G) (haG' : a ∈ G') (has : a ∈ P.smoothSet) {z : φ.model.E 1}
    {z' : φ'.model.E 1} (hz : φ.model.E.toBase 1 z = φ a)
    (hz' : φ'.model.E.toBase 1 z' = φ' a) :
    finrank ℝ (span ℝ (tangentSpace φ.model.E φ.model.C (φ '' (G ∩ A)) z)) =
      finrank ℝ (span ℝ (tangentSpace φ'.model.E φ'.model.C (φ' '' (G' ∩ A)) z')) := by
  have hzs : z ∈ φ.model.E.smoothLvl 1 := by
    change φ.model.E.toBase 1 z ∈ (φ.model.E.smooth : Set (φ.model.E 0))
    rw [hz]; exact (mem_smoothSet_iff hφ (hGφ haG)).1 has
  obtain ⟨n, Wq, T, hT⟩ := φ.model.isPartialQuadrant
  obtain ⟨n', Wq', T', hT'⟩ := φ'.model.isPartialQuadrant
  exact chart_change_of_transport
    (fun E C _ Q _ _ _ w => finrank ℝ (span ℝ (tangentSpace E C Q w)) =
      finrank ℝ (span ℝ (tangentSpace φ.model.E φ.model.C (φ '' (G ∩ A)) z)))
    (fun _ _ _ _ _ _ _ _ _ _ hQ _ h => by rw [← hQ]; exact h)
    (fun _ _ _ _ _ _ _ _ h hF hG _ _ hQ hQ' hQR hQ'R hFQ hGQ _ hz _ _ _ _ _ _ _ _ _ hk => by
      rw [← finrank_span_tangentSpace_eq h hF hG hQ hQ' hQR hQ'R hFQ hGQ hz]; exact hk)
    hφ hφ' hG hG' hGφ hGφ' hQ hQ' haA haG haG' hz hz' hzs T hT T' hT' rfl |>.symm

/-- **The dimension is independent of the choices** (the chart, the data of Definition 4.13, or
any open piece `G` of a chart domain on which `A` is a retract): if `A` has dimension `k` at `a`,
the tangent space at `a` of every such chart model of `A` has dimension `k`. -/
theorem HasDimAt.finrank_eq' {A : Set X} {a : X} {k : ℕ} (h : P.HasDimAt A a k)
    {φ' : MChart X} (hφ' : P.IsChart φ') {G' : Set X} (hG' : IsOpen G') (hGφ' : G' ⊆ φ'.source)
    (hQ' : IsScRetract φ'.model.E φ'.model.C (φ' '' (G' ∩ A))) (haG' : a ∈ G')
    {z' : φ'.model.E 1} (hz' : φ'.model.E.toBase 1 z' = φ' a) :
    finrank ℝ (span ℝ (tangentSpace φ'.model.E φ'.model.C (φ' '' (G' ∩ A)) z')) = k := by
  obtain ⟨haA, d, φ, z, ha, hφ, haφ, hz, hk⟩ := h
  have has : a ∈ P.smoothSet := by
    have := d.apply_mem_smooth hφ haA ha haφ
    exact (mem_smoothSet_iff hφ haφ).2 this
  rw [← hk]
  exact (finrank_tangentSpace_chart_change hφ hφ' (d.toSubData.isOpen_shrink φ) hG'
    (d.toSubData.shrink_subset_source φ) hGφ' (d.toSubData.isScRetract_image φ hφ) hQ' haA
    (d.toSubData.mem_shrink φ haA ha haφ) haG' has hz hz').symm

/-- **The dimension is independent of the choices**, for the chart models of Definition 4.13. -/
theorem HasDimAt.finrank_eq {A : Set X} {a : X} {k : ℕ} (h : P.HasDimAt A a k)
    (d' : P.SubmanifoldData A) {φ' : MChart X} (hφ' : P.IsChart φ') {z' : φ'.model.E 1}
    (ha' : a ∈ d'.V) (haφ' : a ∈ φ'.source) (hz' : φ'.model.E.toBase 1 z' = φ' a) :
    finrank ℝ (span ℝ (tangentSpace φ'.model.E φ'.model.C
      (φ' '' (d'.toSubData.shrink φ' ∩ A)) z')) = k :=
  h.finrank_eq' hφ' (d'.toSubData.isOpen_shrink φ') (d'.toSubData.shrink_subset_source φ')
    (d'.toSubData.isScRetract_image φ' hφ') (d'.toSubData.mem_shrink φ' h.1 ha' haφ') hz'

/-- The dimension of `A` at `a` can be read in any chart model `φ(G ∩ A)` of `A`. -/
theorem hasDimAt_of_finrank {A : Set X} (hA : P.IsSmoothSubmanifold A) {a : X} (haA : a ∈ A)
    {φ : MChart X} (hφ : P.IsChart φ) {G : Set X} (hG : IsOpen G) (hGφ : G ⊆ φ.source)
    (hQ : IsScRetract φ.model.E φ.model.C (φ '' (G ∩ A))) (haG : a ∈ G) {z : φ.model.E 1}
    (hz : φ.model.E.toBase 1 z = φ a) {k : ℕ}
    (hk : finrank ℝ (span ℝ (tangentSpace φ.model.E φ.model.C (φ '' (G ∩ A)) z)) = k) :
    P.HasDimAt A a k := by
  set d := hA.data haA
  refine ⟨haA, d, φ, z, hA.mem_data_V haA, hφ, hGφ haG, hz, ?_⟩
  rw [← hk]
  exact (finrank_tangentSpace_chart_change hφ hφ (d.toSubData.isOpen_shrink φ) hG
    (d.toSubData.shrink_subset_source φ) hGφ (d.toSubData.isScRetract_image φ hφ) hQ haA
    (d.toSubData.mem_shrink φ haA (hA.mem_data_V haA) (hGφ haG)) haG
    (hA.subset_smoothSet haA) hz hz)

/-- **The dimension at a point is unique.** -/
theorem HasDimAt.unique {A : Set X} {a : X} {k k' : ℕ} (h : P.HasDimAt A a k)
    (h' : P.HasDimAt A a k') : k = k' := by
  obtain ⟨-, d, φ, z, ha, hφ, haφ, hz, hk⟩ := h'
  rw [← hk]
  exact (h.finrank_eq d hφ ha haφ hz).symm

/-- Every point of a smooth finite-dimensional submanifold has a dimension. -/
theorem IsSmoothSubmanifold.exists_hasDimAt {A : Set X} (hA : P.IsSmoothSubmanifold A) {a : X}
    (ha : a ∈ A) : ∃ k, P.HasDimAt A a k := by
  obtain ⟨φ, hφ, haφ⟩ := P.exists_isChart_mem_source a
  have hs : φ a ∈ φ.model.E.smooth := (mem_smoothSet_iff hφ haφ).1 (hA.subset_smoothSet ha)
  obtain ⟨z, hz, -⟩ := exists_smoothLvl_one_of_mem_smooth hs
  exact ⟨_, ha, hA.data ha, φ, z, hA.mem_data_V ha, hφ, haφ, hz, rfl⟩

/-- **The dimension is a germ**: for `V` open and `a ∈ V`, `A ∩ V` has dimension `k` at `a` iff
`A` has. -/
theorem hasDimAt_inter_isOpen_iff {A V : Set X} (hA : P.IsSmoothSubmanifold A) (hV : IsOpen V)
    {a : X} (haV : a ∈ V) {k : ℕ} : P.HasDimAt (A ∩ V) a k ↔ P.HasDimAt A a k := by
  have hset : ∀ G : Set X, G ∩ (A ∩ V) = (G ∩ V) ∩ A := fun G => by
    ext; simp only [mem_inter_iff]; tauto
  constructor
  · rintro ⟨⟨haA, -⟩, d, φ, z, ha, hφ, haφ, hz, hk⟩
    have hQ := d.toSubData.isScRetract_image φ hφ
    rw [hset] at hQ hk
    exact hasDimAt_of_finrank hA haA hφ ((d.toSubData.isOpen_shrink φ).inter hV)
      (fun x hx => d.toSubData.shrink_subset_source φ hx.1) hQ
      ⟨d.toSubData.mem_shrink φ ⟨haA, haV⟩ ha haφ, haV⟩ hz hk
  · intro h
    have haA : a ∈ A := h.1
    have hAV := hA.inter_isOpen hV
    set d := hAV.data ⟨haA, haV⟩
    obtain ⟨φ, hφ, haφ⟩ := P.exists_isChart_mem_source a
    have hs : φ a ∈ φ.model.E.smooth := (mem_smoothSet_iff hφ haφ).1 (hA.subset_smoothSet haA)
    obtain ⟨z, hz, -⟩ := exists_smoothLvl_one_of_mem_smooth hs
    refine ⟨⟨haA, haV⟩, d, φ, z, hAV.mem_data_V ⟨haA, haV⟩, hφ, haφ, hz, ?_⟩
    have hQ := d.toSubData.isScRetract_image φ hφ
    rw [hset] at hQ ⊢
    exact h.finrank_eq' hφ ((d.toSubData.isOpen_shrink φ).inter hV)
      (fun x hx => d.toSubData.shrink_subset_source φ hx.1) hQ
      ⟨d.toSubData.mem_shrink φ ⟨haA, haV⟩ (hAV.mem_data_V ⟨haA, haV⟩) haφ, haV⟩ hz

/-- **The dimension is invariant under sc-diffeomorphisms**: if `f : U → U'` is an
sc-diffeomorphism between open subsets of `X` and `A ⊆ U` a smooth finite-dimensional
submanifold, then `f(A)` has dimension `k` at `f(a)` iff `A` has dimension `k` at `a` (in the
chart `ψ ∘ f` (`transportChart`) the chart models of `A` and `f(A)` agree). -/
theorem hasDimAt_image_iff {f g : X → X} {U U' : Set X} (hf : P.IsScDiffeoOn P f g U U')
    {A : Set X} (hA : P.IsSmoothSubmanifold A) (hAU : A ⊆ U) {a : X} (ha : a ∈ A) {k : ℕ} :
    P.HasDimAt (f '' A) (f a) k ↔ P.HasDimAt A a k := by
  -- one direction for every sc-diffeomorphism
  have key : ∀ {f g : X → X} {U U' : Set X}, P.IsScDiffeoOn P f g U U' → ∀ {A : Set X},
      P.IsSmoothSubmanifold A → A ⊆ U → ∀ {a : X}, a ∈ A → ∀ {k : ℕ},
      P.HasDimAt (f '' A) (f a) k → P.HasDimAt A a k := by
    intro f g U U' hf A hA hAU a ha k h
    obtain ⟨ψ, hψ, hfaψ⟩ := P.exists_isChart_mem_source (f a)
    set χ := transportChart hf ψ with hχdef
    have hχ : P.IsChart χ := transportChart_isChart hf hψ
    have haχ : a ∈ χ.source := ⟨hAU ha, hfaψ⟩
    set d := hA.data ha
    set G := d.toSubData.shrink χ with hGdef
    have hGχ : G ⊆ χ.source := d.toSubData.shrink_subset_source χ
    have hGU : G ⊆ U := fun x hx => (hGχ hx).1
    have hfG : f '' G = U' ∩ g ⁻¹' G := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hf.mapsTo (hGU hx), by rw [mem_preimage, hf.left_inv x (hGU hx)]; exact hx⟩
      · rintro ⟨hy, hgy⟩
        exact ⟨g y, hgy, hf.right_inv y hy⟩
    have hfGo : IsOpen (f '' G) := by
      rw [hfG]
      exact hf.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage hf.isScSmoothOn_inv.isOpen
        (d.toSubData.isOpen_shrink χ)
    have hfGψ : f '' G ⊆ ψ.source := by
      rintro _ ⟨x, hx, rfl⟩; exact (hGχ hx).2
    have haG : a ∈ G := d.toSubData.mem_shrink χ ha (hA.mem_data_V ha) haχ
    have himg : χ '' (G ∩ A) = ψ '' (f '' G ∩ f '' A) := by
      rw [← image_inter_on (fun x hx y hy hxy => by
        rw [← hf.left_inv x (hAU hx), ← hf.left_inv y (hGU hy), hxy])]
      rw [← image_comp]
      rfl
    have hQ : IsScRetract χ.model.E χ.model.C (χ '' (G ∩ A)) :=
      d.toSubData.isScRetract_image χ hχ
    have hs : χ a ∈ χ.model.E.smooth := (mem_smoothSet_iff hχ haχ).1 (hA.subset_smoothSet ha)
    obtain ⟨z, hz, -⟩ := exists_smoothLvl_one_of_mem_smooth hs
    refine hasDimAt_of_finrank hA ha hχ (d.toSubData.isOpen_shrink χ) hGχ hQ haG hz ?_
    have hQ' : IsScRetract ψ.model.E ψ.model.C (ψ '' (f '' G ∩ f '' A)) := himg ▸ hQ
    rw [himg]
    exact h.finrank_eq' hψ hfGo hfGψ hQ' ⟨a, haG, rfl⟩ hz
  refine ⟨key hf hA hAU ha, fun h => ?_⟩
  have hfA : P.IsSmoothSubmanifold (f '' A) := hA.image_of_isScDiffeoOn hf hAU
  have hgf : g '' (f '' A) = A := by
    rw [image_image]
    exact (image_congr fun x hx => hf.left_inv x (hAU hx)).trans (image_id' A)
  refine key hf.symm hfA (image_subset_iff.2 fun x hx => hf.mapsTo (hAU hx)) ⟨a, ha, rfl⟩ ?_
  rw [hgf, hf.left_inv a (hAU ha)]
  exact h

variable (P) in
/-- **An `n`-dimensional submanifold** (Remark 9.1.1): a smooth finite-dimensional submanifold
(Definition 4.13 [4.4]) with `dim T_aA = n` at every point. -/
def IsSubmanifoldOfDim (A : Set X) (n : ℕ) : Prop :=
  P.IsSmoothSubmanifold A ∧ ∀ a ∈ A, P.HasDimAt A a n

/-- An open piece of an `n`-dimensional submanifold is `n`-dimensional. -/
theorem IsSubmanifoldOfDim.inter_isOpen {A V : Set X} {n : ℕ} (hA : P.IsSubmanifoldOfDim A n)
    (hV : IsOpen V) : P.IsSubmanifoldOfDim (A ∩ V) n :=
  ⟨hA.1.inter_isOpen hV, fun a ha => (hasDimAt_inter_isOpen_iff hA.1 hV ha.2).2 (hA.2 a ha.1)⟩

/-- The image of an `n`-dimensional submanifold under an sc-diffeomorphism is `n`-dimensional. -/
theorem IsSubmanifoldOfDim.image_of_isScDiffeoOn {f g : X → X} {U U' : Set X}
    (hf : P.IsScDiffeoOn P f g U U') {A : Set X} {n : ℕ} (hA : P.IsSubmanifoldOfDim A n)
    (hAU : A ⊆ U) : P.IsSubmanifoldOfDim (f '' A) n := by
  refine ⟨hA.1.image_of_isScDiffeoOn hf hAU, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  exact (hasDimAt_image_iff hf hA.1 hAU ha).2 (hA.2 a ha)

/-- The dimension of an `n`-dimensional submanifold at each of its points is `n`. -/
theorem IsSubmanifoldOfDim.eq_of_hasDimAt {A : Set X} {n k : ℕ} (hA : P.IsSubmanifoldOfDim A n)
    {a : X} (h : P.HasDimAt A a k) : n = k :=
  (hA.2 a h.1).unique h

end MPolyfold

/-! ### Submanifolds of `ℝⁿ`: images of `C^∞` retractions -/

section Rn

open scoped ContDiff

variable {n : ℕ}

/-- `1₀¹ : ℝⁿ → (ℝⁿ)¹` is sc-smooth (Remark 4.3: the model `(ℝⁿ, ℝⁿ, ℝⁿ)` of the chart of `ℝⁿ` is
an sc⁺-retract). -/
theorem rnPolyfold_isScSmoothMap_toLevelOne (x₀ : (rnPolyfold n).Level 1) :
    (rnPolyfold n).IsScSmoothMap (rnPolyfold n).shift ((rnPolyfold n).toLevelOne x₀) :=
  (MPolyfold.isScSmoothMap_toLevelOne_of_cover x₀ fun r => ⟨rnChart n 0, isChart_rnChart 0,
    mem_univ r, (remark_4_1_3_const (Fin n → ℝ)).2.2 univ univ (rn_relOpen_univ n).isScRetract⟩).2

/-- A `C^∞` retraction `s : ℝⁿ → ℝⁿ` (`s ∘ s = s`) is an sc⁺-retraction of the M-polyfold `ℝⁿ`
(Definition 4.4). -/
theorem rnPolyfold_isScPlusRetractionOn_univ {s : (Fin n → ℝ) → Fin n → ℝ}
    (hs : ContDiff ℝ ∞ s) (hss : ∀ r, s (s r) = s r) :
    (rnPolyfold n).IsScPlusRetractionOn s univ where
  isScSmoothOn := isScSmoothMap_rn_rn_of_contDiff hs
  mapsTo := mapsTo_univ _ _
  idem r _ := hss r
  mem_levelSet r _ := by rw [rnPolyfold_levelSet]; exact mem_univ _
  isScSmoothOn_one x₀ := (rnPolyfold_isScSmoothMap_toLevelOne x₀).comp
    (isScSmoothMap_rn_rn_of_contDiff hs)

/-- **The image of a `C^∞` retraction of `ℝⁿ` is a smooth finite-dimensional submanifold** of the
M-polyfold `ℝⁿ` (Definition 4.13 [4.4], with `V = ℝⁿ`). -/
theorem rnPolyfold_isSmoothSubmanifold_range {s : (Fin n → ℝ) → Fin n → ℝ}
    (hs : ContDiff ℝ ∞ s) (hss : ∀ r, s (s r) = s r) :
    (rnPolyfold n).IsSmoothSubmanifold (range s) := fun a _ =>
  ⟨univ, isOpen_univ, mem_univ a, s, rnPolyfold_isScPlusRetractionOn_univ hs hss,
    by rw [image_univ, inter_univ]⟩

/-- The image of a continuous retraction is closed (it is the fixed point set). -/
theorem isClosed_range_of_idem' {Z : Type*} [TopologicalSpace Z] [T2Space Z] {s : Z → Z}
    (hs : Continuous s) (hss : ∀ r, s (s r) = s r) : IsClosed (range s) := by
  have h : range s = {r | s r = r} :=
    ext fun r => ⟨by rintro ⟨q, rfl⟩; exact hss q, fun h => ⟨r, h⟩⟩
  rw [h]
  exact isClosed_eq hs continuous_id

/-- **The dimension of the image of a `C^∞` retraction** `s` of `ℝⁿ` at `a = s(a)` is the rank of
`Ds(a)` (the tangent space `T_a(s(ℝⁿ)) = Ds(a)ℝⁿ`, Remark 4.14, in the chart `id` of `ℝⁿ`). -/
theorem rnPolyfold_hasDimAt_range {s : (Fin n → ℝ) → Fin n → ℝ} (hs : ContDiff ℝ ∞ s)
    (hss : ∀ r, s (s r) = s r) {a : Fin n → ℝ} (ha : a ∈ range s) :
    (rnPolyfold n).HasDimAt (range s) a
      (finrank ℝ (LinearMap.range (fderiv ℝ s a : (Fin n → ℝ) →ₗ[ℝ] Fin n → ℝ))) := by
  have hU := rn_relOpen_univ n
  let R : ScRetraction (rnSc n) univ := ⟨univ, s, hU, mapsTo_univ _ _,
    IsScSmooth.of_contDiffOn_finiteDimensional hU.isScDomain hs.contDiffOn, fun r _ => hss r⟩
  have hR : R.retract = range s := image_univ
  have hid : ∀ r, (rnChart n 0) r = r := fun r => by rw [rnChart_apply, sub_zero]
  have himg : (rnChart n 0) '' (univ ∩ range s) = range s := by
    rw [univ_inter]
    exact (image_congr fun r _ => hid r).trans (image_id _)
  have hQ : IsScRetract (rnChart n 0).model.E (rnChart n 0).model.C
      ((rnChart n 0) '' (univ ∩ range s)) := by
    rw [himg, ← hR]; exact R.isScRetract
  refine MPolyfold.hasDimAt_of_finrank (rnPolyfold_isSmoothSubmanifold_range hs hss) ha
    (isChart_rnChart 0) isOpen_univ (subset_univ _) hQ (mem_univ a) (z := (a : (rnSc n) 1)) ?_ ?_
  · change (ScBanach.const (Fin n → ℝ)).toBase 1 a = a - 0
    rw [ScBanach.const_toBase, sub_zero]
  · have hz : (a : (rnSc n) 1) ∈ (rnSc n).lvlSet R.retract 1 := by
      rw [ScBanach.mem_lvlSet, ScBanach.const_toBase, hR]; exact ha
    have hd : HasFDerivWithinAt s (scDeriv (E := rnSc n) (F := rnSc n) univ s a) univ a :=
      hasFDerivWithinAt_scDeriv_const' (V := Fin n → ℝ) (F := rnSc n) (U := univ) (f := s)
        R.isSc1 (mem_univ a)
    have hfd : fderiv ℝ s a = scDeriv (E := rnSc n) (F := rnSc n) univ s a :=
      (hasFDerivWithinAt_univ.1 hd).fderiv
    have hT : tangentSpace (rnSc n) univ R.retract (a : (rnSc n) 1) =
        (LinearMap.range (fderiv ℝ s a : (Fin n → ℝ) →ₗ[ℝ] Fin n → ℝ) : Set (Fin n → ℝ)) := by
      rw [tangentSpace_eq_range R hz, hfd, LinearMap.coe_range]
      rfl
    have hset : ((rnChart n 0) '' (univ ∩ range s) : Set ((rnSc n) 0)) = R.retract :=
      himg.trans hR.symm
    erw [hset, hT, span_eq]
    rfl

/-! #### Graphs in `ℝ²` -/

/-- The retraction `(s, t) ↦ (s, β(s))` of `ℝ²` onto the graph of `β : ℝ → ℝ`. -/
def graphRetraction (β : ℝ → ℝ) (r : Fin 2 → ℝ) : Fin 2 → ℝ := ![r 0, β (r 0)]

/-- The graph `{(s, β(s)) | s ∈ ℝ}` of `β : ℝ → ℝ`, a subset of `ℝ²`. -/
def graph2 (β : ℝ → ℝ) : Set (Fin 2 → ℝ) := {r | r 1 = β (r 0)}

theorem graphRetraction_apply_zero (β : ℝ → ℝ) (r : Fin 2 → ℝ) : graphRetraction β r 0 = r 0 :=
  rfl

theorem graphRetraction_apply_one (β : ℝ → ℝ) (r : Fin 2 → ℝ) :
    graphRetraction β r 1 = β (r 0) := rfl

theorem graphRetraction_idem (β : ℝ → ℝ) (r : Fin 2 → ℝ) :
    graphRetraction β (graphRetraction β r) = graphRetraction β r := rfl

theorem range_graphRetraction (β : ℝ → ℝ) : range (graphRetraction β) = graph2 β := by
  ext r
  constructor
  · rintro ⟨q, rfl⟩; rfl
  · intro h
    refine ⟨r, funext fun i => ?_⟩
    fin_cases i
    · rfl
    · exact h.symm

theorem contDiff_graphRetraction {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (graphRetraction β) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · exact contDiff_apply ℝ ℝ (0 : Fin 2)
  · exact hβ.comp (contDiff_apply ℝ ℝ (0 : Fin 2))

/-- **The graph of a `C^∞` function `β : ℝ → ℝ` is a smooth finite-dimensional submanifold** of the
M-polyfold `ℝ²`: it is the image of the sc⁺-retraction `(s, t) ↦ (s, β(s))`. -/
theorem rnPolyfold_isSmoothSubmanifold_graph2 {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) :
    (rnPolyfold 2).IsSmoothSubmanifold (graph2 β) := by
  rw [← range_graphRetraction]
  exact rnPolyfold_isSmoothSubmanifold_range (contDiff_graphRetraction hβ)
    (graphRetraction_idem β)

/-- The graph of a continuous function is closed, so its inclusion into any open `U ⊇ graph` (or
the inclusion of its trace on `U`) is proper. -/
theorem isClosed_graph2 {β : ℝ → ℝ} (hβ : Continuous β) : IsClosed (graph2 β) :=
  isClosed_eq (continuous_apply 1) (hβ.comp (continuous_apply 0))

/-- The derivative of `(s, t) ↦ (s, β(s))` at `a` is `h ↦ h₀ • (1, β'(a₀))`. -/
theorem hasFDerivAt_graphRetraction {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (a : Fin 2 → ℝ) :
    HasFDerivAt (graphRetraction β)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).smulRight
        ![1, deriv β (a 0)]) a := by
  refine hasFDerivAt_pi'.2 fun i => ?_
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) (0 : Fin 2) a
  fin_cases i
  · refine h0.congr_fderiv ?_
    ext h
    simp
  · have h1 := (hβ.differentiable (by simp)).differentiableAt.hasDerivAt (x := a 0)
    refine (h1.comp_hasFDerivAt a h0).congr_fderiv ?_
    ext h
    simp [mul_comm]

/-- **The graph of a `C^∞` function is `1`-dimensional** (the tangent space at `(s, β(s))` is the
line spanned by `(1, β'(s))`). -/
theorem rnPolyfold_isSubmanifoldOfDim_graph2 {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) :
    (rnPolyfold 2).IsSubmanifoldOfDim (graph2 β) 1 := by
  refine ⟨rnPolyfold_isSmoothSubmanifold_graph2 hβ, fun a ha => ?_⟩
  rw [← range_graphRetraction] at ha ⊢
  have h := rnPolyfold_hasDimAt_range (contDiff_graphRetraction hβ) (graphRetraction_idem β) ha
  rw [(hasFDerivAt_graphRetraction hβ a).fderiv] at h
  convert h using 1
  have hrange : LinearMap.range (((ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 2 => ℝ) 0).smulRight ![1, deriv β (a 0)] :
        (Fin 2 → ℝ) →L[ℝ] Fin 2 → ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] Fin 2 → ℝ) =
      span ℝ {![1, deriv β (a 0)]} := by
    ext v
    rw [LinearMap.mem_range, mem_span_singleton]
    constructor
    · rintro ⟨w, rfl⟩; exact ⟨w 0, rfl⟩
    · rintro ⟨c, rfl⟩; exact ⟨fun _ => c, rfl⟩
  rw [hrange, finrank_span_singleton]
  intro h0
  have := congrFun h0 0
  simp at this

end Rn

/-! ### Dimensions of branched ep⁺-subgroupoids (Definition 9.1.2, last paragraph) -/

namespace EpGroupoid

universe u

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ}

namespace LocalBranchingStructure

variable {x : Obj} (B : X.LocalBranchingStructure Θ x)

/-- The submanifolds `Mᵢ` of the local branching structure are all `n`-dimensional. -/
def IsOfDim (n : ℕ) : Prop := ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) n

/-- The dimensions of the `Mᵢ` are determined: two labellings `dim`, `dim'` of the `Mᵢ` by their
dimensions agree (all `Mᵢ` pass through `x`). -/
theorem dim_unique {dim dim' : B.ι → ℕ} (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i))
    (hdim' : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim' i)) : dim = dim' :=
  funext fun i => (hdim i).eq_of_hasDimAt ((hdim' i).2 x (B.mem_M i))

open scoped Classical in
/-- **The `k`-dimensional part** of `Θ` on `U(x)` (the proof of Proposition 9.1.11): for a
labelling `dim` of the `Mᵢ` by dimensions, `Θ_k(y) = ∑_{i ∈ I_k, y ∈ Mᵢ} σᵢ` with
`I_k = {i | dim i = k}`. -/
def dimPart (dim : B.ι → ℕ) (k : ℕ) (y : Obj) : ℚ := ∑ i with dim i = k ∧ y ∈ B.M i, B.σ i

open scoped Classical in
/-- The `k`-dimensional part is represented on `U(x)` by the local branching structure
`(Mᵢ)_{i ∈ I_k}`, `(σᵢ)_{i ∈ I_k}`. -/
def dimPartStructure (dim : B.ι → ℕ) (k : ℕ) : X.LocalBranchingStructure (B.dimPart dim k) x where
  U := B.U
  isOpen_U := B.isOpen_U
  mem_U := B.mem_U
  ι := {i // dim i = k}
  M i := B.M i
  subset_U i := B.subset_U i
  isSmoothSubmanifold i := B.isSmoothSubmanifold i
  mem_M i := B.mem_M i
  isProperMap i := B.isProperMap i
  σ i := B.σ i
  σ_pos i := B.σ_pos i
  eq_sum y _ := by
    unfold dimPart
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_subtype
      (Finset.univ.filter fun i => dim i = k) (by simp) (fun i => if y ∈ B.M i then B.σ i else 0),
      Finset.sum_filter]
    simp only [ite_and]

/-- The `k`-dimensional part is `k`-dimensional. -/
theorem dimPartStructure_isOfDim {dim : B.ι → ℕ}
    (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i)) (k : ℕ) :
    (B.dimPartStructure dim k).IsOfDim k := fun i => by
  obtain ⟨i, hi⟩ := i
  change X.PObj.IsSubmanifoldOfDim (B.M i) k
  rw [← hi]
  exact hdim i

open scoped Classical in
/-- **The dimensional decomposition over `U(x)`** (the proof of Proposition 9.1.11):
`Θ = Θ_0 + ⋯ + Θ_n` on `U(x)`, the sum over the dimensions occurring among the `Mᵢ`. -/
theorem eq_sum_dimPart (dim : B.ι → ℕ) {y : Obj} (hy : y ∈ B.U) :
    Θ y = ∑ k ∈ Finset.univ.image dim, B.dimPart dim k y := by
  rw [B.eq_sum y hy]
  unfold dimPart
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter fun i => y ∈ B.M i)
    (t := Finset.univ.image dim) (g := dim)
    (fun i _ => Finset.mem_image_of_mem dim (Finset.mem_univ i))]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_comm

/-- `Θ_k` vanishes on `U(x)` for `k` not among the dimensions of the `Mᵢ`. -/
theorem dimPart_eq_zero {dim : B.ι → ℕ} {k : ℕ} (hk : ∀ i, dim i ≠ k) (y : Obj) :
    B.dimPart dim k y = 0 := by
  unfold dimPart
  refine Finset.sum_eq_zero fun i hi => ?_
  simp only [Finset.mem_filter] at hi
  exact (hk i hi.2.1).elim

/-- If all `Mᵢ` are `n`-dimensional, `Θ_n = Θ` on `U(x)`. -/
theorem dimPart_eq_of_isOfDim {n : ℕ} {dim : B.ι → ℕ} (hdim : ∀ i, dim i = n) {y : Obj}
    (hy : y ∈ B.U) : B.dimPart dim n y = Θ y := by
  rw [B.eq_sum y hy]
  unfold dimPart
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp [hdim i]

end LocalBranchingStructure

namespace SymmetricBranchingStructure

variable {x : Obj} (S : X.SymmetricBranchingStructure Θ x)

/-- **The action of `G_x` preserves the dimension** (the proof of Proposition 9.1.11): for a
symmetric local branching structure (Lemma 9.1.7) and the labelling `dim` of the `Mᵢ` by
dimensions, `dim (g • i) = dim i`, since `M_{g(i)} = Φ(g)(Mᵢ)` and `Φ(g)` is an
sc-diffeomorphism. -/
theorem dim_smul {dim : S.ι → ℕ} (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (S.M i) (dim i))
    (g : X.Isotropy x) (i : S.ι) : dim (g • i) = dim i := by
  have hMU : S.M i ⊆ S.rep.U := S.U_eq ▸ S.subset_U i
  have h := (hdim i).image_of_isScDiffeoOn (S.rep.isScDiffeoOn_Φ g) hMU
  rw [S.image_M] at h
  exact (hdim (g • i)).eq_of_hasDimAt (h.2 x (S.mem_M (g • i)))

open scoped Classical in
/-- **The `k`-dimensional parts are `G_x`-invariant** (the sets `I_k` are `G_x`-invariant, "the
action of `G_x` preserves dimension"): `Θ_k(Φ(g)(y)) = Θ_k(y)` on `U(x)`, so `Θ_k` is a functor
on `G_x ⋉ U(x)`. -/
theorem dimPart_Φ {dim : S.ι → ℕ} (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (S.M i) (dim i))
    (g : X.Isotropy x) (k : ℕ) {y : Obj} (hy : y ∈ S.U) :
    S.dimPart dim k (S.rep.Φ g y) = S.dimPart dim k y := by
  have hyR : y ∈ S.rep.U := S.U_eq ▸ hy
  have hmem : ∀ i, S.rep.Φ g y ∈ S.M (g • i) ↔ y ∈ S.M i := fun i => by
    rw [← S.image_M]
    constructor
    · rintro ⟨w, hw, hwy⟩
      have hwU : w ∈ S.rep.U := S.U_eq ▸ S.subset_U i hw
      have := congrArg (S.rep.Φ g⁻¹) hwy
      rw [(S.rep.isScDiffeoOn_Φ g).left_inv w hwU, (S.rep.isScDiffeoOn_Φ g).left_inv y hyR]
        at this
      exact this ▸ hw
    · exact fun h => ⟨y, h, rfl⟩
  unfold LocalBranchingStructure.dimPart
  rw [Finset.sum_filter, Finset.sum_filter]
  refine (Fintype.sum_equiv (MulAction.toPerm g) _ _ fun i => ?_).symm
  simp only [MulAction.toPerm_apply, dim_smul S hdim, hmem, S.σ_smul]

end SymmetricBranchingStructure

variable (X) in
/-- **`Θ` is `n`-dimensional** (Definition 9.1.2, last paragraph): at every point of `supp(Θ)`
there is a local branching structure whose submanifolds are all `n`-dimensional. -/
def IsNDimensional (Θ : Obj → ℚ) (n : ℕ) : Prop :=
  ∀ x ∈ supp Θ, ∃ B : X.LocalBranchingStructure Θ x, B.IsOfDim n

/-- The zero functor is `n`-dimensional for every `n` (empty support; the footnote to Definition
9.1.2, "if `Θ` is `n`-dimensional it is not `m`-dimensional for `m ≠ n`", concerns `Θ ≠ 0`). -/
theorem isNDimensional_zero (n : ℕ) : X.IsNDimensional 0 n := fun _ hx =>
  (lt_irrefl (0 : ℚ) hx).elim

/-! ### Proposition 9.1.11: the statement -/

variable (X) in
/-- **The conditions of Proposition 9.1.11**: `(Θ_k)_{k ∈ ℕ}` is a *dimensional decomposition*
of `Θ`: (1) every `Θ_k` is a `k`-dimensional branched ep⁺-subgroupoid, and (2)
`Θ = Θ_0 + Θ_1 + ⋯` (at every object only finitely many `Θ_k` are nonzero). -/
structure IsDimDecomposition (Θ : Obj → ℚ) (Θk : ℕ → Obj → ℚ) : Prop where
  isBranched : ∀ k, X.IsBranchedEpSubgroupoid (Θk k)
  isNDimensional : ∀ k, X.IsNDimensional (Θk k) k
  finite_support : ∀ y, (Function.support fun k => Θk k y).Finite
  eq_finsum : ∀ y, Θ y = ∑ᶠ k, Θk k y

/-- The family `(Θ_k)` is **locally finite**: every object has a neighbourhood on which only
finitely many `Θ_k` are not identically zero. -/
def IsLocallyFiniteFamily (Θk : ℕ → Obj → ℚ) : Prop :=
  ∀ y, ∃ W ∈ 𝓝 y, {k | ∃ z ∈ W, Θk k z ≠ 0}.Finite

variable (X) in
/-- **Proposition 9.1.11, as stated** (p. 407): every branched ep⁺-subgroupoid `Θ` has a dimensional
decomposition `(Θ_k)` "uniquely characterized" by (1) and (2) of `IsDimDecomposition`, and the sum
is locally finite.  As we read it, the uniqueness does not hold:
`not_proposition_9_1_11_rn` gives two decompositions of the indicator of a line in `ℝ²`. -/
def Proposition_9_1_11 : Prop :=
  ∀ Θ, X.IsBranchedEpSubgroupoid Θ →
    (∃! Θk, X.IsDimDecomposition Θ Θk) ∧ ∀ Θk, X.IsDimDecomposition Θ Θk → IsLocallyFiniteFamily Θk

/-! ### Proposition 9.1.12: the statement -/

namespace LocalBranchingStructure

variable {x : Obj}

/-- The dimensional decompositions of two local branching structures `B`, `B'` at `x` (with the
labellings `dim`, `dim'` of their submanifolds by dimensions) **agree near `x`**: on an open
`V ∋ x` inside both domains, `Θ_k = Θ'_k` for every `k`. -/
def DimPartsAgreeNear (B B' : X.LocalBranchingStructure Θ x) (dim : B.ι → ℕ)
    (dim' : B'.ι → ℕ) : Prop :=
  ∃ V : Set Obj, IsOpen V ∧ x ∈ V ∧ V ⊆ B.U ∩ B'.U ∧
    ∀ k, ∀ y ∈ V, B.dimPart dim k y = B'.dimPart dim' k y

/-- The neighbourhood can be taken to be the domain of a natural representation of `G_x`
(Theorem 7.1: "an open `G_x`-invariant neighbourhood `V(x)` with the usual properties"). -/
theorem DimPartsAgreeNear.exists_naturalRep {B B' : X.LocalBranchingStructure Θ x}
    {dim : B.ι → ℕ} {dim' : B'.ι → ℕ} (h : DimPartsAgreeNear B B' dim dim') :
    ∃ R : X.NaturalRep x, R.U ⊆ B.U ∩ B'.U ∧
      ∀ k, ∀ y ∈ R.U, B.dimPart dim k y = B'.dimPart dim' k y := by
  obtain ⟨V, hV, hxV, hVU, hk⟩ := h
  obtain ⟨R, hR⟩ := theorem_7_1_13 X x hV hxV
  exact ⟨R, hR.trans hVU, fun k y hy => hk k y (hR hy)⟩

/-- **Proposition 9.1.12 in the equidimensional case**: if the submanifolds of both local
branching structures are all `n`-dimensional, the decompositions agree on `U ∩ U'` (`Θ_n = Θ`,
`Θ_k = 0` for `k ≠ n`). -/
theorem dimPartsAgreeNear_of_isOfDim {n : ℕ} (B B' : X.LocalBranchingStructure Θ x)
    {dim : B.ι → ℕ} {dim' : B'.ι → ℕ} (hdim : ∀ i, dim i = n) (hdim' : ∀ j, dim' j = n) :
    DimPartsAgreeNear B B' dim dim' := by
  refine ⟨B.U ∩ B'.U, B.isOpen_U.inter B'.isOpen_U, ⟨B.mem_U, B'.mem_U⟩, subset_rfl,
    fun k y hy => ?_⟩
  by_cases hk : k = n
  · subst hk
    rw [B.dimPart_eq_of_isOfDim hdim hy.1, B'.dimPart_eq_of_isOfDim hdim' hy.2]
  · rw [B.dimPart_eq_zero (fun i h => hk (h.symm.trans (hdim i))),
      B'.dimPart_eq_zero (fun j h => hk (h.symm.trans (hdim' j)))]

end LocalBranchingStructure

variable (X) in
/-- **Proposition 9.1.12, the statement** (p. 408; proof in §9.6.1, pp. 452–457): for a branched
ep⁺-subgroupoid `Θ`, an object `x` and two local branching structures at `x` whose submanifolds
have constant dimensions, the dimensional decompositions agree on an open `G_x`-invariant
neighbourhood of `x` (`DimPartsAgreeNear`, equivalently with the domain of a natural
representation, `DimPartsAgreeNear.exists_naturalRep`).  Not proved here: see the module
docstring for what the proof in §9.6.1 needs. -/
def Proposition_9_1_12 : Prop :=
  ∀ Θ : Obj → ℚ, X.IsBranchedEpSubgroupoid Θ → ∀ (x : Obj) (B B' : X.LocalBranchingStructure Θ x)
    (dim : B.ι → ℕ) (dim' : B'.ι → ℕ), (∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i)) →
    (∀ j, X.PObj.IsSubmanifoldOfDim (B'.M j) (dim' j)) →
    LocalBranchingStructure.DimPartsAgreeNear B B' dim dim'

/-! ### Branched ep⁺-subgroupoids of the trivial ep-groupoid of `ℝⁿ` -/

section TrivialRn

variable {n : ℕ}

/-- In the trivial ep-groupoid of `ℝⁿ`, `π : ℝⁿ → |ℝⁿ|` is a homeomorphism, so `|supp(Θ)|` is
metrizable, hence paracompact, for every `Θ` (Definition 9.1.2 (1)). -/
theorem paracompactSpace_orbitSupp_trivial_rn (Θ : (Fin n → ℝ) → ℚ) :
    ParacompactSpace ((trivial (rnPolyfold n)).orbitSupp Θ) := by
  set X := trivial (rnPolyfold n)
  have hinj : Function.Injective X.π := fun a b h => by
    obtain ⟨φ, h1, h2⟩ := X.π_eq_π_iff.1 h
    exact h1.symm.trans h2
  let e : (Fin n → ℝ) ≃ₜ X.OrbitSpace := Equiv.toHomeomorphOfContinuousOpen
    (Equiv.ofBijective _ ⟨hinj, X.surjective_π⟩) X.continuous_π X.proposition_7_1_8
  have h := (e.image (supp Θ)).paracompactSpace_iff.1 inferInstance
  have heq : e '' supp Θ = X.orbitSupp Θ := rfl
  rwa [heq] at h

open scoped Classical in
/-- **The local branching structure of a weighted sum of closed submanifolds of `ℝⁿ`**: for
finitely many closed smooth submanifolds `Mᵢ` and weights `σᵢ > 0`, the functor
`Θ(y) = ∑_{i : y ∈ Mᵢ} σᵢ` has at `x` the local branching structure on
`U = {y | y ∈ Mᵢ ⇒ x ∈ Mᵢ}` (the complement of the `Mᵢ` not through `x`) formed by the
`Mᵢ ∩ U`, `x ∈ Mᵢ`. -/
def localBranchingStructure_sum_rn {ι : Type} [Fintype ι] (M : ι → Set (Fin n → ℝ))
    (σ : ι → ℚ) (hσ : ∀ i, 0 < σ i) (hM : ∀ i, (rnPolyfold n).IsSmoothSubmanifold (M i))
    (hc : ∀ i, IsClosed (M i)) (x : Fin n → ℝ) :
    (trivial (rnPolyfold n)).LocalBranchingStructure (fun y => ∑ i with y ∈ M i, σ i) x :=
  have hU : IsOpen {y | ∀ i, y ∈ M i → x ∈ M i} := by
    have : {y | ∀ i, y ∈ M i → x ∈ M i} = ⋂ i, {y | y ∈ M i → x ∈ M i} := by ext; simp
    rw [this]
    refine isOpen_iInter_of_finite fun i => ?_
    by_cases hx : x ∈ M i
    · simp [hx]
    · simp only [hx, imp_false]
      exact (hc i).isOpen_compl
  { U := {y | ∀ i, y ∈ M i → x ∈ M i}
    isOpen_U := hU
    mem_U := fun _ h => h
    ι := {i // x ∈ M i}
    M i := M i.1 ∩ {y | ∀ i, y ∈ M i → x ∈ M i}
    subset_U _ := inter_subset_right
    isSmoothSubmanifold i := (hM i.1).inter_isOpen hU
    mem_M i := ⟨i.2, fun _ h => h⟩
    isProperMap i := by
      refine (isProperMap_inclusion_iff _).2 ?_
      convert (hc i.1).preimage continuous_subtype_val using 1
      ext y
      exact ⟨fun h => h.1, fun h => ⟨h, y.2⟩⟩
    σ i := σ i.1
    σ_pos i := hσ i.1
    eq_sum y hy := by
      rw [Finset.sum_filter, Finset.sum_filter]
      have h1 : (∑ i, if y ∈ M i then σ i else 0) =
          ∑ i ∈ Finset.univ.filter (fun i => x ∈ M i), (if y ∈ M i then σ i else 0) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hyi : y ∈ M i
        · simp [hyi, hy i hyi]
        · simp [hyi]
      rw [h1, Finset.sum_subtype (Finset.univ.filter fun i => x ∈ M i) (p := fun i => x ∈ M i)
        (by simp)]
      congr 1
      funext i
      by_cases hyi : y ∈ M i.1
      · simp [hyi, hy]
      · simp [hyi] }

open scoped Classical in
/-- **A weighted sum of closed submanifolds of `ℝⁿ` is a branched ep⁺-subgroupoid** of the
trivial ep-groupoid of `ℝⁿ`: `Θ(y) = ∑_{i : y ∈ Mᵢ} σᵢ` for finitely many closed smooth
submanifolds `Mᵢ` and weights `σᵢ > 0`. -/
theorem isBranchedEpSubgroupoid_sum_rn {ι : Type} [Fintype ι] (M : ι → Set (Fin n → ℝ))
    (σ : ι → ℚ) (hσ : ∀ i, 0 < σ i) (hM : ∀ i, (rnPolyfold n).IsSmoothSubmanifold (M i))
    (hc : ∀ i, IsClosed (M i)) :
    (trivial (rnPolyfold n)).IsBranchedEpSubgroupoid (fun y => ∑ i with y ∈ M i, σ i) where
  nonneg _ := Finset.sum_nonneg fun i _ => (hσ i).le
  isFunctorial _ := rfl
  support_subset y _ := by
    change y ∈ (rnPolyfold n).smoothSet
    rw [TrivialBundle.rnPolyfold_smoothSet]; exact mem_univ y
  paracompactSpace_orbitSupp := paracompactSpace_orbitSupp_trivial_rn _
  localBranching x _ := ⟨localBranchingStructure_sum_rn M σ hσ hM hc x⟩

open scoped Classical in
/-- If the closed submanifolds `Mᵢ` are all `k`-dimensional, `Θ = ∑ σᵢ 1_{Mᵢ}` is
`k`-dimensional. -/
theorem isNDimensional_sum_rn {ι : Type} [Fintype ι] (M : ι → Set (Fin n → ℝ))
    (σ : ι → ℚ) (hσ : ∀ i, 0 < σ i) {k : ℕ} (hM : ∀ i, (rnPolyfold n).IsSubmanifoldOfDim (M i) k)
    (hc : ∀ i, IsClosed (M i)) :
    (trivial (rnPolyfold n)).IsNDimensional (fun y => ∑ i with y ∈ M i, σ i) k := fun x _ =>
  ⟨localBranchingStructure_sum_rn M σ hσ (fun i => (hM i).1) hc x,
    fun i => (hM i.1).inter_isOpen (localBranchingStructure_sum_rn M σ hσ (fun i => (hM i).1)
      hc x).isOpen_U⟩

/-- **The local branching structure of the indicator of a locally closed submanifold of `ℝⁿ`**:
for `A ⊆ W`, `W` open, `A` closed in `W` and a smooth submanifold, the indicator `1_A` has at
`x ∈ A` the local branching structure `U = W`, one submanifold `A` with weight `1`. -/
def localBranchingStructure_indicator_rn {A W : Set (Fin n → ℝ)} (hW : IsOpen W) (hAW : A ⊆ W)
    (hcl : IsClosed ((↑) ⁻¹' A : Set W)) (hA : (rnPolyfold n).IsSmoothSubmanifold A) {x : Fin n → ℝ}
    (hx : x ∈ A) : (trivial (rnPolyfold n)).LocalBranchingStructure (A.indicator 1) x where
  U := W
  isOpen_U := hW
  mem_U := hAW hx
  ι := Unit
  M _ := A
  subset_U _ := hAW
  isSmoothSubmanifold _ := hA
  mem_M _ := hx
  isProperMap _ := (isProperMap_inclusion_iff hAW).2 hcl
  σ _ := 1
  σ_pos _ := one_pos
  eq_sum y _ := by
    by_cases hy : y ∈ A
    · simp [hy]
    · simp [hy]

theorem supp_indicator_one (A : Set (Fin n → ℝ)) :
    supp (A.indicator (1 : (Fin n → ℝ) → ℚ)) = A := by
  ext y
  by_cases hy : y ∈ A
  · simp [supp, hy]
  · simp [supp, hy]

/-- **The indicator of a locally closed `k`-dimensional submanifold of `ℝⁿ` is a `k`-dimensional
branched ep⁺-subgroupoid** of the trivial ep-groupoid of `ℝⁿ`. -/
theorem isBranchedEpSubgroupoid_indicator_rn {A W : Set (Fin n → ℝ)} (hW : IsOpen W)
    (hAW : A ⊆ W) (hcl : IsClosed ((↑) ⁻¹' A : Set W)) {k : ℕ}
    (hA : (rnPolyfold n).IsSubmanifoldOfDim A k) :
    (trivial (rnPolyfold n)).IsBranchedEpSubgroupoid (A.indicator 1) ∧
      (trivial (rnPolyfold n)).IsNDimensional (A.indicator 1) k := by
  refine ⟨⟨fun y => ?_, fun _ => rfl, fun y _ => ?_, paracompactSpace_orbitSupp_trivial_rn _,
    fun x hx => ?_⟩, fun x hx => ?_⟩
  · by_cases hy : y ∈ A
    · simp [hy]
    · simp [hy]
  · change y ∈ (rnPolyfold n).smoothSet
    rw [TrivialBundle.rnPolyfold_smoothSet]; exact mem_univ y
  · rw [supp_indicator_one] at hx
    exact ⟨localBranchingStructure_indicator_rn hW hAW hcl hA.1 hx⟩
  · rw [supp_indicator_one] at hx
    exact ⟨localBranchingStructure_indicator_rn hW hAW hcl hA.1 hx, fun _ => hA⟩

end TrivialRn

/-! ### Remark 9.1.3 (b): local branching structures are not unique -/

namespace LocalBranchingStructure

variable {x : Obj}

/-- A local branching structure for `Θ` is one for every `Θ'` equal to `Θ`. -/
def ofEq (B : X.LocalBranchingStructure Θ x) {Θ' : Obj → ℚ} (h : ∀ y, Θ y = Θ' y) :
    X.LocalBranchingStructure Θ' x :=
  { B with eq_sum := fun y hy => (h y).symm.trans (B.eq_sum y hy) }

end LocalBranchingStructure

section Remark913

open scoped ContDiff Classical

/-- The curve `s ↦ (s, β(s))` in `ℝ²`. -/
def curve2 (β : ℝ → ℝ) (s : ℝ) : Fin 2 → ℝ := ![s, β s]

theorem continuous_curve2 {β : ℝ → ℝ} (hβ : Continuous β) : Continuous (curve2 β) := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact continuous_id
  · exact hβ

theorem curve2_zero {β : ℝ → ℝ} (hβ : β 0 = 0) : curve2 β 0 = 0 := by
  ext i; fin_cases i
  · rfl
  · exact hβ

theorem curve2_mem_graph2_iff (β γ : ℝ → ℝ) (s : ℝ) : curve2 β s ∈ graph2 γ ↔ β s = γ s :=
  Iff.rfl

/-- A continuous curve through `0` meets every neighbourhood of `0` at a positive and at a negative
time. -/
theorem exists_curve2_mem {β : ℝ → ℝ} (hβ : Continuous β) (hβ0 : β 0 = 0)
    {V : Set (Fin 2 → ℝ)} (hV : IsOpen V) (h0V : (0 : Fin 2 → ℝ) ∈ V) :
    ∃ s > 0, curve2 β s ∈ V ∧ curve2 β (-s) ∈ V := by
  have hpre : IsOpen (curve2 β ⁻¹' V) := hV.preimage (continuous_curve2 hβ)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hpre 0 (by
    change curve2 β 0 ∈ V; rw [curve2_zero hβ0]; exact h0V)
  refine ⟨ε / 2, half_pos hε, hball ?_, hball ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]; linarith
  · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg, abs_of_pos (half_pos hε)]; linarith

/-- The functor of Remark 9.1.3 (b): `Θ(p) = ∑_{i : p ∈ Gᵢ} 1` for the graphs `G₁`, `G₂` of
`β₁`, `β₂`, i.e. `Θ(p) = #{i ∈ {1, 2} | p ∈ Gᵢ}` (`thetaGraphs_eq_card`). -/
def thetaGraphs (β₁ β₂ : ℝ → ℝ) (p : Fin 2 → ℝ) : ℚ :=
  ∑ i with p ∈ ![graph2 β₁, graph2 β₂] i, (1 : ℚ)

theorem thetaGraphs_eq_card (β₁ β₂ : ℝ → ℝ) (p : Fin 2 → ℝ) :
    thetaGraphs β₁ β₂ p = (Finset.univ.filter fun i => p ∈ ![graph2 β₁, graph2 β₂] i).card := by
  rw [thetaGraphs, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem thetaGraphs_apply (β₁ β₂ : ℝ → ℝ) (p : Fin 2 → ℝ) :
    thetaGraphs β₁ β₂ p =
      (if p 1 = β₁ (p 0) then 1 else 0) + (if p 1 = β₂ (p 0) then 1 else 0) := by
  rw [thetaGraphs, Finset.sum_filter, Fin.sum_univ_two]
  rfl

/-- **The two descriptions of `Θ` agree** when at every `s` one of `β₁(s)`, `β₂(s)` vanishes:
the graphs of `β₁`, `β₂` and those of `γ₁ = 0`, `γ₂ = β₁ + β₂` carry the same counting
function. -/
theorem thetaGraphs_eq {β₁ β₂ : ℝ → ℝ} (h : ∀ s, β₁ s = 0 ∨ β₂ s = 0) (p : Fin 2 → ℝ) :
    thetaGraphs β₁ β₂ p = thetaGraphs 0 (β₁ + β₂) p := by
  rw [thetaGraphs_apply, thetaGraphs_apply]
  simp only [Pi.zero_apply, Pi.add_apply]
  rcases h (p 0) with h1 | h2
  · simp only [h1, zero_add]
  · simp only [h2, add_zero]
    rw [add_comm]

/-- **The hypotheses of Remark 9.1.3 (b)** on `β₁, β₂ : ℝ → ℝ`: smooth, `β₁(s) = 0` for `s ≤ 0`,
`β₁(s) > 0` for `s > 0`, `β₂(s) > 0` for `s < 0`, `β₂(s) = 0` for `s ≥ 0`. -/
structure Remark913Hyp (β₁ β₂ : ℝ → ℝ) : Prop where
  contDiff₁ : ContDiff ℝ ∞ β₁
  contDiff₂ : ContDiff ℝ ∞ β₂
  eq_zero₁ : ∀ s ≤ 0, β₁ s = 0
  pos₁ : ∀ s, 0 < s → 0 < β₁ s
  pos₂ : ∀ s < 0, 0 < β₂ s
  eq_zero₂ : ∀ s, 0 ≤ s → β₂ s = 0

/-- The hypotheses of Remark 9.1.3 (b) are satisfiable: `β₁ = expNegInvGlue`
(`e^{-1/s}` for `s > 0`, `0` for `s ≤ 0`) and `β₂(s) = β₁(-s)`. -/
theorem remark913Hyp_expNegInvGlue :
    Remark913Hyp expNegInvGlue (fun s => expNegInvGlue (-s)) where
  contDiff₁ := expNegInvGlue.contDiff
  contDiff₂ := expNegInvGlue.contDiff.comp contDiff_neg
  eq_zero₁ _ hs := expNegInvGlue.zero_of_nonpos hs
  pos₁ _ hs := expNegInvGlue.pos_of_pos hs
  pos₂ _ hs := expNegInvGlue.pos_of_pos (neg_pos.2 hs)
  eq_zero₂ _ hs := expNegInvGlue.zero_of_nonpos (neg_nonpos.2 hs)

theorem graphs2_isSubmanifoldOfDim {β γ : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (hγ : ContDiff ℝ ∞ γ) :
    ∀ i, (rnPolyfold 2).IsSubmanifoldOfDim (![graph2 β, graph2 γ] i) 1 := fun i => by
  fin_cases i
  · exact rnPolyfold_isSubmanifoldOfDim_graph2 hβ
  · exact rnPolyfold_isSubmanifoldOfDim_graph2 hγ

theorem graphs2_isClosed {β γ : ℝ → ℝ} (hβ : Continuous β) (hγ : Continuous γ) :
    ∀ i, IsClosed (![graph2 β, graph2 γ] i) := fun i => by
  fin_cases i
  · exact isClosed_graph2 hβ
  · exact isClosed_graph2 hγ

namespace Remark913Hyp

variable {β₁ β₂ : ℝ → ℝ} (h : Remark913Hyp β₁ β₂)
include h

theorem eq_zero_or : ∀ s, β₁ s = 0 ∨ β₂ s = 0 := fun s =>
  (le_total s 0).imp (h.eq_zero₁ s) (h.eq_zero₂ s)

/-- `γ₂ = β₁ + β₂` is smooth, vanishes at `0` and is positive for `s ≠ 0` (as the text requires
of `γ₂`). -/
theorem γ₂_pos {s : ℝ} (hs : s ≠ 0) : 0 < (β₁ + β₂) s := by
  rcases hs.lt_or_gt with hs | hs
  · rw [Pi.add_apply, h.eq_zero₁ s hs.le, zero_add]; exact h.pos₂ s hs
  · rw [Pi.add_apply, h.eq_zero₂ s hs.le, add_zero]; exact h.pos₁ s hs

/-- The local branching structure of `Θ` at `x` by the graphs of `β₁`, `β₂` (weights `1`). -/
def structureβ (x : Fin 2 → ℝ) :
    (trivial (rnPolyfold 2)).LocalBranchingStructure (thetaGraphs β₁ β₂) x :=
  localBranchingStructure_sum_rn _ 1 (fun _ => one_pos)
    (fun i => (graphs2_isSubmanifoldOfDim h.contDiff₁ h.contDiff₂ i).1)
    (graphs2_isClosed h.contDiff₁.continuous h.contDiff₂.continuous) x

/-- The local branching structure of the same `Θ` at `x` by the graphs of `γ₁ = 0` and
`γ₂ = β₁ + β₂` (weights `1`). -/
def structureγ (x : Fin 2 → ℝ) :
    (trivial (rnPolyfold 2)).LocalBranchingStructure (thetaGraphs β₁ β₂) x :=
  (localBranchingStructure_sum_rn _ 1 (fun _ => one_pos)
    (fun i => (graphs2_isSubmanifoldOfDim contDiff_const
      (h.contDiff₁.add h.contDiff₂) i).1)
    (graphs2_isClosed continuous_const
      (h.contDiff₁.continuous.add h.contDiff₂.continuous)) x).ofEq
    fun p => (thetaGraphs_eq h.eq_zero_or p).symm

/-- **The reading of `γ₂`**: the text asks of the second structure only `γ₁ = 0` and `γ₂(s) > 0`
for `s ≠ 0`; describing the same `Θ` forces `γ₂ = β₁ + β₂`. -/
theorem eq_add_of_thetaGraphs_eq {γ : ℝ → ℝ} (hγ : ∀ p, thetaGraphs β₁ β₂ p = thetaGraphs 0 γ p) :
    γ = β₁ + β₂ := by
  funext s
  by_contra hne
  have hp := hγ (curve2 (β₁ + β₂) s)
  rw [thetaGraphs_apply, thetaGraphs_apply] at hp
  change ((if β₁ s + β₂ s = β₁ s then 1 else 0) + if β₁ s + β₂ s = β₂ s then 1 else 0 : ℚ) =
    (if β₁ s + β₂ s = 0 then 1 else 0) + (if β₁ s + β₂ s = γ s then 1 else 0) at hp
  have hne' : β₁ s + β₂ s ≠ γ s := fun h' => hne h'.symm
  rcases h.eq_zero_or s with h1 | h2
  · rw [h1, zero_add] at hp hne'
    rw [if_pos rfl, if_neg hne'] at hp
    linarith
  · rw [h2, add_zero] at hp hne'
    rw [if_pos rfl, if_neg hne'] at hp
    linarith

end Remark913Hyp

/-- **Remark 9.1.3 (b) (2017: Remark 9.2 (b)), p. 403**: on `X = ℝ²` (only identity morphisms),
for `β₁, β₂` as in the remark, `Θ(p) = #{i | p ∈ Gᵢ}` (`Gᵢ` the graph of `βᵢ`, weights `1`) is a
`1`-dimensional branched ep⁺-subgroupoid; it is also described by the graphs of `γ₁ = 0` and
`γ₂ = β₁ + β₂` (`γ₂(s) > 0` for `s ≠ 0`); and the two local branching structures at the origin
are different "even close to `x`": no submanifold of the one agrees with a submanifold of the
other on any neighbourhood of `0`. -/
theorem remark_9_1_3_b {β₁ β₂ : ℝ → ℝ} (h : Remark913Hyp β₁ β₂) :
    (trivial (rnPolyfold 2)).IsBranchedEpSubgroupoid (thetaGraphs β₁ β₂) ∧
      (trivial (rnPolyfold 2)).IsNDimensional (thetaGraphs β₁ β₂) 1 ∧
      (∀ p, thetaGraphs β₁ β₂ p = thetaGraphs 0 (β₁ + β₂) p) ∧
      ∀ V : Set (Fin 2 → ℝ), IsOpen V → (0 : Fin 2 → ℝ) ∈ V →
        ∀ i j, (h.structureβ 0).M i ∩ V ≠ (h.structureγ 0).M j ∩ V := by
  refine ⟨isBranchedEpSubgroupoid_sum_rn _ 1 (fun _ => one_pos)
      (fun i => (graphs2_isSubmanifoldOfDim h.contDiff₁ h.contDiff₂ i).1)
      (graphs2_isClosed h.contDiff₁.continuous h.contDiff₂.continuous),
    isNDimensional_sum_rn _ 1 (fun _ => one_pos)
      (graphs2_isSubmanifoldOfDim h.contDiff₁ h.contDiff₂)
      (graphs2_isClosed h.contDiff₁.continuous h.contDiff₂.continuous),
    thetaGraphs_eq h.eq_zero_or, fun V hV h0V i j => ?_⟩
  intro heq
  have h10 : β₁ 0 = 0 := h.eq_zero₁ 0 le_rfl
  have h20 : β₂ 0 = 0 := h.eq_zero₂ 0 le_rfl
  have hall : ∀ (β γ : ℝ → ℝ), β 0 = 0 → γ 0 = 0 → ∀ k,
      (0 : Fin 2 → ℝ) ∈ ![graph2 β, graph2 γ] k := fun β γ hβ hγ k => by
    fin_cases k
    · exact hβ.symm
    · exact hγ.symm
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  have key : ∀ y, y ∈ V → y ∈ ![graph2 β₁, graph2 β₂] i →
      y ∈ ![graph2 0, graph2 (β₁ + β₂)] j := fun y hyV hy => by
    have hmem : y ∈ (h.structureβ 0).M ⟨i, hi⟩ ∩ V :=
      ⟨⟨hy, fun k _ => hall β₁ β₂ h10 h20 k⟩, hyV⟩
    rw [heq] at hmem
    exact hmem.1.1
  clear heq hi hj
  obtain ⟨s, hs, hV1, hV1'⟩ := exists_curve2_mem h.contDiff₁.continuous h10 hV h0V
  obtain ⟨t, ht, hV2, hV2'⟩ := exists_curve2_mem h.contDiff₂.continuous h20 hV h0V
  obtain ⟨r, hr, hV0, hV0'⟩ := exists_curve2_mem (β := 0) continuous_const rfl hV h0V
  fin_cases i <;> fin_cases j
  · -- `G(β₁)` against `G(γ₁)`: the point `(s, β₁(s))`, `s > 0`
    have : β₁ s = 0 := key _ hV1 rfl
    exact (h.pos₁ s hs).ne' this
  · -- `G(β₁)` against `G(γ₂)`: the point `(-r, 0)`
    have := key _ hV0' (h.eq_zero₁ (-r) (neg_nonpos.2 hr.le)).symm
    exact (h.γ₂_pos (neg_ne_zero.2 hr.ne')).ne this
  · -- `G(β₂)` against `G(γ₁)`: the point `(-t, β₂(-t))`
    have : β₂ (-t) = 0 := key _ hV2' rfl
    exact (h.pos₂ (-t) (neg_neg_iff_pos.2 ht)).ne' this
  · -- `G(β₂)` against `G(γ₂)`: the point `(r, 0)`
    have := key _ hV0 (h.eq_zero₂ r hr.le).symm
    exact (h.γ₂_pos hr.ne').ne this

end Remark913

/-! ### Proposition 9.1.11: the uniqueness does not hold as we read it -/

section Counterexample

open scoped ContDiff Classical

/-- The `x`-axis `L = {(s, 0)}` of `ℝ²` (the graph of `0`). -/
abbrev axis2 : Set (Fin 2 → ℝ) := graph2 0

theorem axis2_isSubmanifoldOfDim : (rnPolyfold 2).IsSubmanifoldOfDim axis2 1 :=
  rnPolyfold_isSubmanifoldOfDim_graph2 contDiff_const

theorem isClosed_axis2 : IsClosed axis2 := isClosed_graph2 continuous_const

theorem zero_mem_axis2 : (0 : Fin 2 → ℝ) ∈ axis2 := rfl

/-- A point of `ℝⁿ` is a `0`-dimensional submanifold (the image of a constant retraction, whose
derivative vanishes). -/
theorem rnPolyfold_isSubmanifoldOfDim_singleton {n : ℕ} (p : Fin n → ℝ) :
    (rnPolyfold n).IsSubmanifoldOfDim {p} 0 := by
  refine ⟨rnPolyfold_isSmoothSubmanifold_singleton n p, fun a ha => ?_⟩
  have hr : range (fun _ : Fin n → ℝ => p) = {p} := range_const
  have h := rnPolyfold_hasDimAt_range (s := fun _ : Fin n → ℝ => p) contDiff_const
    (fun _ => rfl) (hr ▸ ha)
  rw [hr, fderiv_const_apply] at h
  convert h using 1
  rw [ContinuousLinearMap.toLinearMap_zero, LinearMap.range_zero, finrank_bot]

/-- The two dimensional decompositions of `Θ = 1_L` (`L` the `x`-axis of `ℝ²`): `Θ_0 = 1_{0}`,
`Θ_1 = 1_{L ∖ {0}}` ... -/
def decompA : ℕ → (Fin 2 → ℝ) → ℚ := fun k =>
  if k = 0 then ({0} : Set (Fin 2 → ℝ)).indicator 1
  else if k = 1 then (axis2 ∩ {0}ᶜ).indicator 1 else 0

/-- ... and `Θ_0 = 0`, `Θ_1 = 1_L`. -/
def decompB : ℕ → (Fin 2 → ℝ) → ℚ := fun k => if k = 1 then axis2.indicator 1 else 0

theorem indicator_singleton_zero_branched :
    (trivial (rnPolyfold 2)).IsBranchedEpSubgroupoid (({0} : Set (Fin 2 → ℝ)).indicator 1) ∧
      (trivial (rnPolyfold 2)).IsNDimensional (({0} : Set (Fin 2 → ℝ)).indicator 1) 0 :=
  isBranchedEpSubgroupoid_indicator_rn isOpen_univ (subset_univ _)
    (isClosed_singleton.preimage continuous_subtype_val) (rnPolyfold_isSubmanifoldOfDim_singleton 0)

theorem indicator_axis2_branched :
    (trivial (rnPolyfold 2)).IsBranchedEpSubgroupoid (axis2.indicator 1) ∧
      (trivial (rnPolyfold 2)).IsNDimensional (axis2.indicator 1) 1 :=
  isBranchedEpSubgroupoid_indicator_rn isOpen_univ (subset_univ _)
    (isClosed_axis2.preimage continuous_subtype_val) axis2_isSubmanifoldOfDim

/-- `1_{L ∖ {0}}` is a `1`-dimensional branched ep⁺-subgroupoid (`L ∖ {0}` is closed in the open
set `ℝ² ∖ {0}`). -/
theorem indicator_axis2_diff_branched :
    (trivial (rnPolyfold 2)).IsBranchedEpSubgroupoid ((axis2 ∩ {0}ᶜ).indicator 1) ∧
      (trivial (rnPolyfold 2)).IsNDimensional ((axis2 ∩ {0}ᶜ).indicator 1) 1 := by
  refine isBranchedEpSubgroupoid_indicator_rn isOpen_compl_singleton inter_subset_right ?_
    (axis2_isSubmanifoldOfDim.inter_isOpen isOpen_compl_singleton)
  convert isClosed_axis2.preimage (continuous_subtype_val (p := fun y => y ∈ ({0}ᶜ : Set _)))
    using 1
  ext y
  exact ⟨fun h => h.1, fun h => ⟨h, y.2⟩⟩

theorem decompA_isDimDecomposition :
    (trivial (rnPolyfold 2)).IsDimDecomposition (axis2.indicator 1) decompA where
  isBranched k := by
    rcases k with _ | _ | k
    · exact indicator_singleton_zero_branched.1
    · exact indicator_axis2_diff_branched.1
    · exact isBranchedEpSubgroupoid_zero _
  isNDimensional k := by
    rcases k with _ | _ | k
    · exact indicator_singleton_zero_branched.2
    · exact indicator_axis2_diff_branched.2
    · exact isNDimensional_zero _
  finite_support y := by
    refine (finite_le_nat 1).subset fun k hk => ?_
    by_contra hk'
    have hk2 : ¬ k ≤ 1 := hk'
    have h0 : k ≠ 0 := by omega
    have h1 : k ≠ 1 := by omega
    exact hk (by
      change decompA k y = 0
      unfold decompA
      rw [if_neg h0, if_neg h1]
      rfl)
  eq_finsum y := by
    rw [finsum_eq_sum_of_support_subset (s := {0, 1}) _ fun k hk => by
      by_contra hk'
      simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff,
        not_or] at hk'
      exact hk (by simp [decompA, hk'.1, hk'.2])]
    rw [Finset.sum_pair zero_ne_one]
    simp only [decompA, if_true, one_ne_zero, if_false]
    by_cases hy0 : y = 0
    · subst hy0; simp [zero_mem_axis2]
    · by_cases hyL : y ∈ axis2
      · simp [hy0, hyL]
      · simp [hy0, hyL]

theorem decompB_isDimDecomposition :
    (trivial (rnPolyfold 2)).IsDimDecomposition (axis2.indicator 1) decompB where
  isBranched k := by
    by_cases hk : k = 1
    · subst hk; exact indicator_axis2_branched.1
    · simp only [decompB, hk, if_false]; exact isBranchedEpSubgroupoid_zero _
  isNDimensional k := by
    by_cases hk : k = 1
    · subst hk; exact indicator_axis2_branched.2
    · simp only [decompB, hk, if_false]; exact isNDimensional_zero _
  finite_support y := by
    refine (finite_singleton 1).subset fun k hk => ?_
    by_contra hk'
    exact hk (by
      change decompB k y = 0
      unfold decompB
      rw [if_neg (fun h => hk' (mem_singleton_iff.2 h))]
      rfl)
  eq_finsum y := by
    rw [finsum_eq_single _ 1 fun k hk => by simp [decompB, hk]]
    simp [decompB]

/-- **Proposition 9.1.11, as stated, does not hold as we read it**: the indicator `Θ = 1_L` of the
`x`-axis `L` of `ℝ²` (trivial ep-groupoid) has the two dimensional decompositions
`Θ_0 = 1_{0}`, `Θ_1 = 1_{L ∖ {0}}` and `Θ_0 = 0`, `Θ_1 = 1_L` (all other `Θ_k = 0`): in both,
every `Θ_k` is a `k`-dimensional branched ep⁺-subgroupoid and `Θ = Θ_0 + Θ_1`.  The decomposition
the proof constructs is the second one (its `supp(Θ_k)` are closed in `supp(Θ)`, which
`supp(Θ_1) = L ∖ {0}` in the first is not). -/
theorem not_proposition_9_1_11_rn : ¬ (trivial (rnPolyfold 2)).Proposition_9_1_11 := by
  intro hP
  obtain ⟨⟨Θk, -, huniq⟩, -⟩ := hP _ indicator_axis2_branched.1
  have e := (huniq _ decompA_isDimDecomposition).trans (huniq _ decompB_isDimDecomposition).symm
  have := congrFun (congrFun e 0) 0
  simp [decompA, decompB] at this

end Counterexample

end EpGroupoid

end Polyfold
