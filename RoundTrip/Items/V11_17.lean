import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V11_17

/-!
Round trip for V11_17 (2021 Theorem 11.3.3, the proof for an equivalence, pp. 537–538).

The item lists the definitions `LocalBranchingStructure.mapU`, `LocalBranchingStructure.mapDiffeo`
(a local branching structure moved by an sc-diffeomorphism between open subsets) and the structure
`EpFunctor.TransportChart` (vocabulary), and 23 theorems.  `A` is the conjunction of the types of
the theorems, universes at `0` (`Obj Mor Obj' Mor' : Type`; the three Part I lemmas
`HasDimAt.of_image`, `hasDimAt_image_iff_of_isScDiffeoOn`, `IsSubmanifoldOfDim.image_isScDiffeoOn`
have two universe parameters, both at `0`).

`B` (for an equivalence `F`): `TransportB` (a local branching structure `B` of a branched `Θ` at
`x` and `ψ : F(x) → y` give an open `W ∋ x` in `U(x)` on which `ψ̂ ∘ F` is an sc-diffeomorphism
onto an open set, and a local branching structure of `F_*Θ` at `y` with domain `(ψ̂ ∘ F)(W)`,
sheets `(ψ̂ ∘ F)(Mᵢ ∩ W)` and the same weights), and `Thm1133B` (properties (1)–(6) for `F_*`,
`F^*`, for branched `Θ`).

* `A ⇒ B` (`A_to_B`): `Thm1133B` is read off `A`'s conjuncts (closedness, compactness,
  orbifold/manifold type and dimensional decompositions; `F.IsEquivalence` supplies fullness).
  `TransportB` is proved from the vocabulary: `W = U ∩ F⁻¹(U(ψ)) ∩ U(x)` with `U` a domain on
  which `F` is an sc-diffeomorphism and `U(ψ)` the source of the chosen sheet through `ψ` (on
  which `ψ̂` is an sc-diffeomorphism); `F` restricted to `W` composed with `ψ̂` restricted to
  `F(W)` is an sc-diffeomorphism `W → W'`; `F_*Θ ∘ (ψ̂ ∘ F) = Θ` on `W` by the morphisms
  `(s|U(ψ))⁻¹(F u) : F(u) → ψ̂(F(u))` (non-item `pushforwardTheta_eq`); `B'` is the item's own
  `mapDiffeo` along this diffeomorphism, whose domain `W' ∩ g⁻¹(U(x) ∩ W)` equals `(ψ̂ ∘ F)(W)`
  because `W ⊆ U(x)`; the sheets and weights are those of `mapDiffeo` by `rfl`.  The proof
  fields of `mapDiffeo` use the banned `mem_image_iff_of_mem_mapU`, `mapU` is used in the
  statement of `mem_image_iff_of_mem_mapU`; hence `#rt_check_soft` (see below).
* `B ⇒ A` fails for a genuine reason (`A` is more general): many conjuncts of `A` hold beyond
  equivalences and beyond branched ep⁺-subgroupoids — `isClosedBranched_pullbackTheta`,
  `isOrbifoldType_push/pullbackTheta`, `orbitSupp_pullbackTheta` and
  `exists_pushforwardTheta_eq_apply` for every functor `F`, `isCompactBranched_pushforwardTheta`,
  `orbitSupp_pushforwardTheta` and `exists_mem_supp_of_mem_supp_pushforwardTheta` for every full
  `F`, closedness/compactness/manifold type and `n`-dimensionality for merely functorial `Θ`;
  `mem_image_iff_of_mem_mapU`, `isOfDim_mapDiffeo` and the three Part I lemmas on dimensions of
  submanifolds under sc-diffeomorphisms between different M-polyfolds are about arbitrary
  sc-diffeomorphisms, not about `F_*`, `F^*`.  `B` says nothing about these.  The text's content
  (`B_to_A_core` below: (1), (2) and (6) for equivalences) does follow from `B`.
-/

namespace RoundTrip.V11_17
open Polyfold Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  type_of% @Polyfold.EpFunctor.isBranchedEpSubgroupoid_pullbackTheta.{0} ∧
  type_of% @Polyfold.EpFunctor.isBranchedEpSubgroupoid_pushforwardTheta.{0} ∧
  type_of% @Polyfold.EpFunctor.exists_localBranchingStructure_pushforwardTheta.{0} ∧
  type_of% @Polyfold.EpFunctor.exists_mem_supp_of_mem_supp_pushforwardTheta.{0} ∧
  type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.mem_image_iff_of_mem_mapU.{0} ∧
  type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.isOfDim_mapDiffeo.{0} ∧
  type_of% @Polyfold.EpFunctor.orbitSupp_pullbackTheta.{0} ∧
  type_of% @Polyfold.EpFunctor.orbitSupp_pushforwardTheta.{0} ∧
  type_of% @Polyfold.EpFunctor.isClosedBranched_pushforwardTheta.{0} ∧
  type_of% @Polyfold.EpFunctor.isClosedBranched_pullbackTheta.{0} ∧
  type_of% @Polyfold.EpFunctor.isCompactBranched_pushforwardTheta.{0} ∧
  type_of% @Polyfold.EpFunctor.isCompactBranched_pullbackTheta.{0} ∧
  type_of% @Polyfold.EpFunctor.isOrbifoldType_pushforwardTheta.{0} ∧
  type_of% @Polyfold.EpFunctor.isOrbifoldType_pullbackTheta.{0} ∧
  type_of% @Polyfold.EpFunctor.isManifoldType_pushforwardTheta.{0} ∧
  type_of% @Polyfold.EpFunctor.isManifoldType_pullbackTheta.{0} ∧
  type_of% @Polyfold.EpFunctor.isNDimensional_pullbackTheta.{0} ∧
  type_of% @Polyfold.EpFunctor.isNDimensional_pushforwardTheta.{0} ∧
  type_of% @Polyfold.EpFunctor.exists_pushforwardTheta_eq_apply.{0} ∧
  type_of% @Polyfold.EpFunctor.isDimDecomposition_pushforwardTheta.{0} ∧
  type_of% @Polyfold.EpFunctor.isDimDecomposition_pullbackTheta.{0} ∧
  type_of% @Polyfold.MPolyfold.HasDimAt.of_image.{0, 0} ∧
  type_of% @Polyfold.MPolyfold.hasDimAt_image_iff_of_isScDiffeoOn.{0, 0} ∧
  type_of% @Polyfold.MPolyfold.IsSubmanifoldOfDim.image_isScDiffeoOn.{0, 0}

theorem A_holds : A :=
  ⟨@EpFunctor.isBranchedEpSubgroupoid_pullbackTheta,
    @EpFunctor.isBranchedEpSubgroupoid_pushforwardTheta,
    @EpFunctor.exists_localBranchingStructure_pushforwardTheta,
    @EpFunctor.exists_mem_supp_of_mem_supp_pushforwardTheta,
    @EpGroupoid.LocalBranchingStructure.mem_image_iff_of_mem_mapU,
    @EpGroupoid.LocalBranchingStructure.isOfDim_mapDiffeo,
    @EpFunctor.orbitSupp_pullbackTheta, @EpFunctor.orbitSupp_pushforwardTheta,
    @EpFunctor.isClosedBranched_pushforwardTheta, @EpFunctor.isClosedBranched_pullbackTheta,
    @EpFunctor.isCompactBranched_pushforwardTheta, @EpFunctor.isCompactBranched_pullbackTheta,
    @EpFunctor.isOrbifoldType_pushforwardTheta, @EpFunctor.isOrbifoldType_pullbackTheta,
    @EpFunctor.isManifoldType_pushforwardTheta, @EpFunctor.isManifoldType_pullbackTheta,
    @EpFunctor.isNDimensional_pullbackTheta, @EpFunctor.isNDimensional_pushforwardTheta,
    @EpFunctor.exists_pushforwardTheta_eq_apply,
    @EpFunctor.isDimDecomposition_pushforwardTheta, @EpFunctor.isDimDecomposition_pullbackTheta,
    @MPolyfold.HasDimAt.of_image, @MPolyfold.hasDimAt_image_iff_of_isScDiffeoOn,
    @MPolyfold.IsSubmanifoldOfDim.image_isScDiffeoOn⟩

section Transport

variable {Obj Mor Obj' Mor' : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']

/-- `TransportB`, proved from the vocabulary (`mapDiffeo`) and the non-item
`pushforwardTheta_eq`. -/
theorem transportB (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor') (F : EpFunctor X Y)
    (hF : F.IsEquivalence) : TransportB X Y F := by
  intro Θ hΘ x B ψ y hs ht
  obtain ⟨U, V, g, hxU, hU⟩ := hF.isLocalScDiffeo_obj x
  set S := Y.sheetAt ψ with hSdef
  have hS : Y.PObj.IsScDiffeoOn Y.PObj (Y.hat ψ) (fun z => Y.src (S.tgtInv z)) S.srcSet
      S.tgtSet := Y.isScDiffeoOn_hat ψ
  set W := U ∩ F.obj ⁻¹' S.srcSet ∩ B.U with hWdef
  have hWo : IsOpen W :=
    (hU.isOpen_source.inter (S.isScDiffeoOn_src.isOpen_target.preimage F.continuous_obj')).inter
      B.isOpen_U
  have hWU : W ⊆ U := fun u hu => hu.1.1
  have hxW : x ∈ W := ⟨⟨hxU, by
    show F.obj x ∈ S.srcSet
    rw [← hs]; exact Y.src_mem_sheetAt ψ⟩, B.mem_U⟩
  have h1 := hU.restrict hWo hWU
  have hV1o : IsOpen (V ∩ g ⁻¹' W) := h1.isOpen_target
  have hV1S : V ∩ g ⁻¹' W ⊆ S.srcSet := by
    intro z hz
    have h := hz.2.1.2
    rw [mem_preimage, hU.right_inv z hz.1] at h
    exact h
  have h2 := hS.restrict hV1o hV1S
  have hd := h2.comp h1
  have hxy : (Y.hat ψ ∘ F.obj) x = y := by
    simp only [Function.comp_apply]
    rw [← hs, Y.hat_src, ht]
  have hΘW : ∀ u ∈ W, F.pushforwardTheta Θ ((Y.hat ψ ∘ F.obj) u) = Θ u := by
    intro u hu
    have hFu : F.obj u ∈ S.srcSet := hu.1.2
    refine EpFunctor.pushforwardTheta_eq hF.full hΘ.isFunctorial
      ⟨S.srcInv (F.obj u), S.isScDiffeoOn_src.right_inv _ hFu, rfl⟩
  refine ⟨W, hWo, hxW, fun u hu => hu.2, ⟨_, _, hd.isOpen_target, hd⟩,
    B.mapDiffeo hd hxW hxy hΘW, ?_, Equiv.refl _, fun i => ⟨rfl, rfl⟩⟩
  -- the domain `W' ∩ g⁻¹(U(x) ∩ W)` of `mapDiffeo` is `(ψ̂ ∘ F)(W)`
  ext z
  constructor
  · rintro ⟨hz, hz'⟩
    exact ⟨_, hz'.2, hd.right_inv z hz⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨hd.mapsTo hu, by rw [mem_preimage, hd.left_inv u hu]; exact ⟨hu.2, hu⟩⟩

end Transport

theorem A_to_B : A → B := by
  rintro ⟨hpullB, hpushB, -, -, -, -, -, -, hclPush, hclPull, hcpPush, hcpPull, horbPush,
    horbPull, hmanPush, hmanPull, -, -, -, hdimPush, hdimPull, -, -, -⟩
  intro Obj Mor Obj' Mor' _ _ _ _ _ _ _ _ _ _ _ _ X Y F hF
  refine ⟨transportB X Y F hF, fun Θ hΘ => hpushB hF hΘ, fun Θ' hΘ' => hpullB hF hΘ',
    fun Θ hΘ hc => hclPush hF hΘ.isFunctorial hc, fun Θ' hΘ' hc => hclPull F hΘ'.isFunctorial hc,
    fun Θ hΘ hc => hcpPush F hF.full hΘ.isFunctorial hc,
    fun Θ' hΘ' hc => hcpPull hF hΘ'.isFunctorial hc,
    fun Θ _ h => horbPush F h, fun Θ' _ h => horbPull F h,
    fun Θ hΘ h => hmanPush hF hΘ.isFunctorial h, fun Θ' _ h => hmanPull hF h,
    fun Θ Θk _ h => hdimPush hF h, fun Θ' Θk _ h => hdimPull hF h⟩

/-- What `B` does give: the text's (1), (2) and (6) for an equivalence. -/
theorem B_to_A_core (hB : B) :
    type_of% @Polyfold.EpFunctor.isBranchedEpSubgroupoid_pullbackTheta.{0} ∧
    type_of% @Polyfold.EpFunctor.isBranchedEpSubgroupoid_pushforwardTheta.{0} := by
  refine ⟨?_, ?_⟩
  · intro Obj Mor Obj' Mor' _ _ _ _ _ _ _ _ _ _ _ _ X Y F hF Θ' hΘ'
    exact (hB Obj Mor Obj' Mor' X Y F hF).2.2.1 Θ' hΘ'
  · intro Obj Mor Obj' Mor' _ _ _ _ _ _ _ _ _ _ _ _ X Y F hF Θ hΘ
    exact (hB Obj Mor Obj' Mor' X Y F hF).2.1 Θ hΘ

#rt_check_soft RoundTrip.V11_17.A_to_B [Polyfold.EpFunctor.isBranchedEpSubgroupoid_pullbackTheta,
  Polyfold.EpFunctor.isBranchedEpSubgroupoid_pushforwardTheta,
  Polyfold.EpFunctor.exists_localBranchingStructure_pushforwardTheta,
  Polyfold.EpFunctor.exists_mem_supp_of_mem_supp_pushforwardTheta,
  Polyfold.EpGroupoid.LocalBranchingStructure.mem_image_iff_of_mem_mapU,
  Polyfold.EpGroupoid.LocalBranchingStructure.isOfDim_mapDiffeo,
  Polyfold.EpFunctor.orbitSupp_pullbackTheta, Polyfold.EpFunctor.orbitSupp_pushforwardTheta,
  Polyfold.EpFunctor.isClosedBranched_pushforwardTheta,
  Polyfold.EpFunctor.isClosedBranched_pullbackTheta,
  Polyfold.EpFunctor.isCompactBranched_pushforwardTheta,
  Polyfold.EpFunctor.isCompactBranched_pullbackTheta,
  Polyfold.EpFunctor.isOrbifoldType_pushforwardTheta,
  Polyfold.EpFunctor.isOrbifoldType_pullbackTheta,
  Polyfold.EpFunctor.isManifoldType_pushforwardTheta,
  Polyfold.EpFunctor.isManifoldType_pullbackTheta,
  Polyfold.EpFunctor.isNDimensional_pullbackTheta,
  Polyfold.EpFunctor.isNDimensional_pushforwardTheta,
  Polyfold.EpFunctor.exists_pushforwardTheta_eq_apply,
  Polyfold.EpFunctor.isDimDecomposition_pushforwardTheta,
  Polyfold.EpFunctor.isDimDecomposition_pullbackTheta,
  Polyfold.MPolyfold.HasDimAt.of_image, Polyfold.MPolyfold.hasDimAt_image_iff_of_isScDiffeoOn,
  Polyfold.MPolyfold.IsSubmanifoldOfDim.image_isScDiffeoOn]

#rt_check RoundTrip.V11_17.B_to_A_core [Polyfold.EpFunctor.isBranchedEpSubgroupoid_pullbackTheta,
  Polyfold.EpFunctor.isBranchedEpSubgroupoid_pushforwardTheta,
  Polyfold.EpFunctor.exists_localBranchingStructure_pushforwardTheta,
  Polyfold.EpFunctor.exists_mem_supp_of_mem_supp_pushforwardTheta,
  Polyfold.EpGroupoid.LocalBranchingStructure.mem_image_iff_of_mem_mapU,
  Polyfold.EpGroupoid.LocalBranchingStructure.isOfDim_mapDiffeo,
  Polyfold.EpFunctor.orbitSupp_pullbackTheta, Polyfold.EpFunctor.orbitSupp_pushforwardTheta,
  Polyfold.EpFunctor.isClosedBranched_pushforwardTheta,
  Polyfold.EpFunctor.isClosedBranched_pullbackTheta,
  Polyfold.EpFunctor.isCompactBranched_pushforwardTheta,
  Polyfold.EpFunctor.isCompactBranched_pullbackTheta,
  Polyfold.EpFunctor.isOrbifoldType_pushforwardTheta,
  Polyfold.EpFunctor.isOrbifoldType_pullbackTheta,
  Polyfold.EpFunctor.isManifoldType_pushforwardTheta,
  Polyfold.EpFunctor.isManifoldType_pullbackTheta,
  Polyfold.EpFunctor.isNDimensional_pullbackTheta,
  Polyfold.EpFunctor.isNDimensional_pushforwardTheta,
  Polyfold.EpFunctor.exists_pushforwardTheta_eq_apply,
  Polyfold.EpFunctor.isDimDecomposition_pushforwardTheta,
  Polyfold.EpFunctor.isDimDecomposition_pullbackTheta,
  Polyfold.MPolyfold.HasDimAt.of_image, Polyfold.MPolyfold.hasDimAt_image_iff_of_isScDiffeoOn,
  Polyfold.MPolyfold.IsSubmanifoldOfDim.image_isScDiffeoOn]

#rt_overlap RoundTrip.V11_17.A_to_B [Polyfold.EpFunctor.isBranchedEpSubgroupoid_pullbackTheta,
  Polyfold.EpFunctor.isBranchedEpSubgroupoid_pushforwardTheta,
  Polyfold.EpFunctor.exists_localBranchingStructure_pushforwardTheta,
  Polyfold.EpFunctor.exists_mem_supp_of_mem_supp_pushforwardTheta,
  Polyfold.EpGroupoid.LocalBranchingStructure.mem_image_iff_of_mem_mapU,
  Polyfold.EpGroupoid.LocalBranchingStructure.isOfDim_mapDiffeo,
  Polyfold.EpFunctor.orbitSupp_pullbackTheta, Polyfold.EpFunctor.orbitSupp_pushforwardTheta,
  Polyfold.EpFunctor.isClosedBranched_pushforwardTheta,
  Polyfold.EpFunctor.isClosedBranched_pullbackTheta,
  Polyfold.EpFunctor.isCompactBranched_pushforwardTheta,
  Polyfold.EpFunctor.isCompactBranched_pullbackTheta,
  Polyfold.EpFunctor.isOrbifoldType_pushforwardTheta,
  Polyfold.EpFunctor.isOrbifoldType_pullbackTheta,
  Polyfold.EpFunctor.isManifoldType_pushforwardTheta,
  Polyfold.EpFunctor.isManifoldType_pullbackTheta,
  Polyfold.EpFunctor.isNDimensional_pullbackTheta,
  Polyfold.EpFunctor.isNDimensional_pushforwardTheta,
  Polyfold.EpFunctor.exists_pushforwardTheta_eq_apply,
  Polyfold.EpFunctor.isDimDecomposition_pushforwardTheta,
  Polyfold.EpFunctor.isDimDecomposition_pullbackTheta,
  Polyfold.MPolyfold.HasDimAt.of_image, Polyfold.MPolyfold.hasDimAt_image_iff_of_isScDiffeoOn,
  Polyfold.MPolyfold.IsSubmanifoldOfDim.image_isScDiffeoOn]

end RoundTrip.V11_17
