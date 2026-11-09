import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V11_21

/-!
Round trip for V11_21 (2021 Theorem 11.3.5, p. 539: orientations under generalized
isomorphisms, with the proof's step, pp. 539–540).

The item lists the definitions `OrTangent.map`, `SubmanifoldOrientation.mapDiffeo`,
`OrientedBranchingStructure.mapDiffeo` (vocabulary) and eight theorems; `A` is the conjunction
of the types of the theorems, universes at `0` (the Part I lemmas `IsOrientedAt.map_tangentMapOn`,
`SubmanifoldOrientation.mapDiffeo_tangent` have two universe parameters, both at `0`).

`B = TheoremB ∧ MoveB`: for every representative `d` of a generalized isomorphism, `d.pushSection`
and `d.pullSection` carry orientations of branched `Θ`, `Θ'` to orientations of `d.pushTheta Θ`,
`d.pullTheta Θ'` (**no further hypothesis**); and the step: an oriented local branching
structure is moved by `ψ̂ ∘ F` with the same weights and the pushed-forward orientations.

* `A ⇒ B` fails, because every orientation theorem of `A` (`isOrientation_pushSection`,
  `isOrientation_pullSection`, `theorem_11_3_5_push`, `theorem_11_3_5_pull`) assumes
  `HasIndependentTangentSums Θ` (resp. `Θ'`): the independence of `∑ σᵢ T_xMᵢ` from the local
  branching structure, i.e. Theorem 9.2.1 (1).  The project proves it only under extra hypotheses
  (good points, tangent slices, Proposition 9.1.12, graph charts on `ℝⁿ`); it is satisfiable
  (e.g. `hasIndependentTangentSums_indicator`), but is not known for every branched `Θ`, and
  `B` asserts the conclusion without it.  Supplying it would mean proving Theorem 9.2.1 (1) in
  general.  With the hypothesis added to `B`'s `TheoremB` (`BInd`, which `B` implies by
  weakening), `A ⇒ BInd` holds (`A_to_BInd`): since `d.pushSection = Φ_* F^*` and
  `d.pullSection = F_* Φ^*` by definition, `A`'s `isOrientation_pushSection`,
  `isOrientation_pullSection` apply to the two legs of any representative `d` (with the non-item
  `isBranchedEpSubgroupoid_pullbackTheta`, `hasIndependentTangentSums_pullbackTheta`;
  `theorem_10_3_10` makes `Φ` an equivalence).  (The route through `theorem_11_3_5_push/pull`
  and `pushSection_homMk` is not allowed: `pushSection_homMk` rests on the non-item
  `isOrientedAt_map_tangent_obj`, built on the banned `IsOrientedAt.map_tangentMapOn`.)
  `MoveB` is the vocabulary `OrientedBranchingStructure.mapDiffeo` along the explicit
  sc-diffeomorphism `ψ̂ ∘ F` of V11_17, with `A`'s `SubmanifoldOrientation.mapDiffeo_tangent`
  and the non-item `restrict_tangent` for the orientations.  The vocabulary
  `SubmanifoldOrientation.mapDiffeo` (inside `OrientedBranchingStructure.mapDiffeo`) proves its
  `isOrientedAt` field with the banned `IsOrientedAt.map_tangentMapOn`, so the check is
  `#rt_check_soft`.
* `B ⇒ A` fails (`A` has content `B` lacks): `B` gives `theorem_11_3_5_push/pull` outright
  (`B_to_A_core`, with `d = rep f`), but `A` also contains general lemmas not in `B`:
  `TransportChart.tangentMor_ψ_tangent_obj` (`Tψ_u ∘ TF = TQ` on `TW`),
  `IsOrientedAt.map_tangentMapOn`, `SubmanifoldOrientation.mapDiffeo_tangent`,
  `orientedSum_mapDiffeo` (for arbitrary sc-diffeomorphisms), and the equivalence-level
  `isOrientation_pushSection`, `isOrientation_pullSection` for ep-functors `F` (not diagrams).
-/

namespace RoundTrip.V11_21
open Polyfold Polyfold.EPLocalization Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  type_of% @Polyfold.EpFunctor.TransportChart.tangentMor_ψ_tangent_obj.{0} ∧
  type_of% @Polyfold.MPolyfold.IsOrientedAt.map_tangentMapOn.{0, 0} ∧
  type_of% @Polyfold.MPolyfold.SubmanifoldOrientation.mapDiffeo_tangent.{0, 0} ∧
  type_of% @Polyfold.EpGroupoid.OrientedBranchingStructure.orientedSum_mapDiffeo.{0} ∧
  type_of% @Polyfold.EpFunctor.isOrientation_pushSection.{0} ∧
  type_of% @Polyfold.EpFunctor.isOrientation_pullSection.{0} ∧
  type_of% @Polyfold.EPLocalization.EPLoc.theorem_11_3_5_push.{0} ∧
  type_of% @Polyfold.EPLocalization.EPLoc.theorem_11_3_5_pull.{0}

theorem A_holds : A :=
  ⟨@EpFunctor.TransportChart.tangentMor_ψ_tangent_obj, @MPolyfold.IsOrientedAt.map_tangentMapOn,
    @MPolyfold.SubmanifoldOrientation.mapDiffeo_tangent,
    @EpGroupoid.OrientedBranchingStructure.orientedSum_mapDiffeo,
    @EpFunctor.isOrientation_pushSection, @EpFunctor.isOrientation_pullSection,
    @EPLoc.theorem_11_3_5_push, @EPLoc.theorem_11_3_5_pull⟩

/-- `TheoremB` with Theorem 9.2.1's independence `HasIndependentTangentSums` added to the
hypotheses. -/
def TheoremBInd : Prop :=
  ∀ (X Y : EP.{0}) (f : EPLoc.of X ⟶ EPLoc.of Y), EPLoc.IsGeneralizedIso f →
    ∀ d : Diagram X Y, EPLoc.homMk d = f →
      (∀ (Θ : X.Obj → ℚ) (T : X.Obj → X.X.PObj.OrTangent →₀ ℚ),
        X.X.IsBranchedEpSubgroupoid Θ → X.X.HasIndependentTangentSums Θ →
          X.X.IsOrientation Θ T → Y.X.IsOrientation (d.pushTheta Θ) (d.pushSection T)) ∧
      (∀ (Θ' : Y.Obj → ℚ) (T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ),
        Y.X.IsBranchedEpSubgroupoid Θ' → Y.X.HasIndependentTangentSums Θ' →
          Y.X.IsOrientation Θ' T' → X.X.IsOrientation (d.pullTheta Θ') (d.pullSection T'))

/-- `B` with the independence hypothesis. -/
def BInd : Prop := TheoremBInd ∧ MoveB

/-- `B ⇒ BInd` (weakening). -/
theorem B_to_BInd (hB : B) : BInd :=
  ⟨fun X Y f hf d hd => ⟨fun Θ T hΘ _ hT => (hB.1 X Y f hf d hd).1 Θ T hΘ hT,
    fun Θ' T' hΘ' _ hT' => (hB.1 X Y f hf d hd).2 Θ' T' hΘ' hT'⟩, hB.2⟩

/-- `MoveB`, from `A`'s `mapDiffeo_tangent` and the vocabulary `OrientedBranchingStructure.mapDiffeo`
along the sc-diffeomorphism `ψ̂ ∘ F` (built as in V11_17). -/
theorem moveB_of
    (htan : type_of% @Polyfold.MPolyfold.SubmanifoldOrientation.mapDiffeo_tangent.{0, 0}) :
    MoveB := by
  intro Obj Mor Obj' Mor' _ _ _ _ _ _ _ _ _ _ _ _ X Y F hF Θ hΘ x B ψ y hs ht
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
    exact EpFunctor.pushforwardTheta_eq hF.full hΘ.isFunctorial
      ⟨S.srcInv (F.obj u), S.isScDiffeoOn_src.right_inv _ hFu, rfl⟩
  refine ⟨W, hWo, hxW, fun u hu => hu.2, _, _, hd, hd.isOpen_target,
    B.mapDiffeo hd hxW hxy hΘW, ?_, Equiv.refl _, fun i => ⟨rfl, rfl, fun z hz => ?_⟩⟩
  · ext z
    constructor
    · rintro ⟨hz, hz'⟩
      exact ⟨_, hz'.2, hd.right_inv z hz⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨hd.mapsTo hu, by rw [mem_preimage, hd.left_inv u hu]; exact ⟨hu.2, hu⟩⟩
  · have h := htan ((B.orient i).restrict hd.isScSmoothOn.isOpen)
      ((B.isSmoothSubmanifold i).inter_isOpen hd.isScSmoothOn.isOpen) hd inter_subset_right hz
    rw [MPolyfold.SubmanifoldOrientation.restrict_tangent _ _ hz.2] at h
    exact h

/-- **`A ⇒ BInd`**: `A` gives `B` once the independence is assumed. -/
theorem A_to_BInd (hA : A) : BInd := by
  obtain ⟨-, -, htan, -, hpushF, hpullF, -, -⟩ := hA
  refine ⟨fun X Y f hf d hd => ?_, moveB_of htan⟩
  have hΦ : d.Φ.IsEquivalence := (EPLoc.theorem_10_3_10 d).1.1 (hd ▸ hf)
  -- `d.pushSection = Φ_* F^*`, `d.pullSection = F_* Φ^*` (by definition), so `A`'s
  -- equivalence-level conjuncts apply to the two legs of `d` directly
  refine ⟨fun Θ T hΘ hind hT => ?_, fun Θ' T' hΘ' hind' hT' => ?_⟩
  · exact hpushF hΦ (EpFunctor.isBranchedEpSubgroupoid_pullbackTheta d.isEquivalence_F hΘ)
      (EpFunctor.hasIndependentTangentSums_pullbackTheta d.isEquivalence_F hind)
      (hpullF d.isEquivalence_F hind hT)
  · exact hpushF d.isEquivalence_F (EpFunctor.isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ')
      (EpFunctor.hasIndependentTangentSums_pullbackTheta hΦ hind')
      (hpullF hΦ hind' hT')

/-- What `B` gives: `theorem_11_3_5_push`, `theorem_11_3_5_pull` (on `rep f`; the independence
hypothesis is not needed). -/
theorem B_to_A_core (hB : B) :
    type_of% @Polyfold.EPLocalization.EPLoc.theorem_11_3_5_push.{0} ∧
    type_of% @Polyfold.EPLocalization.EPLoc.theorem_11_3_5_pull.{0} :=
  ⟨fun {X Y f} hf {Θ T} hΘ _ hT =>
      (hB.1 X Y f hf (EPLoc.rep f) (EPLoc.homMk_rep f)).1 Θ T hΘ hT,
    fun {X Y f} hf {Θ' T'} hΘ' _ hT' =>
      (hB.1 X Y f hf (EPLoc.rep f) (EPLoc.homMk_rep f)).2 Θ' T' hΘ' hT'⟩

#rt_check_soft RoundTrip.V11_21.A_to_BInd [Polyfold.EpFunctor.TransportChart.tangentMor_ψ_tangent_obj,
  Polyfold.MPolyfold.IsOrientedAt.map_tangentMapOn,
  Polyfold.MPolyfold.SubmanifoldOrientation.mapDiffeo_tangent,
  Polyfold.EpGroupoid.OrientedBranchingStructure.orientedSum_mapDiffeo,
  Polyfold.EpFunctor.isOrientation_pushSection, Polyfold.EpFunctor.isOrientation_pullSection,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_5_push,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_5_pull]
#rt_check RoundTrip.V11_21.B_to_A_core [Polyfold.EpFunctor.TransportChart.tangentMor_ψ_tangent_obj,
  Polyfold.MPolyfold.IsOrientedAt.map_tangentMapOn,
  Polyfold.MPolyfold.SubmanifoldOrientation.mapDiffeo_tangent,
  Polyfold.EpGroupoid.OrientedBranchingStructure.orientedSum_mapDiffeo,
  Polyfold.EpFunctor.isOrientation_pushSection, Polyfold.EpFunctor.isOrientation_pullSection,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_5_push,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_5_pull]
#rt_overlap RoundTrip.V11_21.A_to_BInd [Polyfold.EpFunctor.TransportChart.tangentMor_ψ_tangent_obj,
  Polyfold.MPolyfold.IsOrientedAt.map_tangentMapOn,
  Polyfold.MPolyfold.SubmanifoldOrientation.mapDiffeo_tangent,
  Polyfold.EpGroupoid.OrientedBranchingStructure.orientedSum_mapDiffeo,
  Polyfold.EpFunctor.isOrientation_pushSection, Polyfold.EpFunctor.isOrientation_pullSection,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_5_push,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_5_pull]

end RoundTrip.V11_21
