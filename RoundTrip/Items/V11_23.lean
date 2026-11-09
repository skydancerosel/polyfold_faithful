import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V11_23

/-!
Round trip for V11_23 (2021 Theorem 11.3.7, p. 541: `(Tf)_*TΘ = T(f_*Θ)`,
`(Tf)^*TΘ' = T(f^*Θ')`).

The item lists sixteen theorems; `A` is the conjunction of their types.  **Universes**: `B` lives
in universe `1` (`X Y : EP.{1}`, because the tangent ep-groupoid and the tangent diagram are only
defined on `EP.{max u 1}`), so `A` is instantiated to match: the theorems on `EP.{max u 1}`
(`tangentFunctor_map_eq`, `theorem_11_3_7_push/pull`) at `u = 0` (i.e. on `EP.{1}`), the theorems
on `Type u` / `EP.{u}` (the equivalence-level and local lemmas, `hasIndependentTangentSums_*`) at
`u = 1`, and the two Part I lemmas (two universe parameters) at `1, 1`.

`B`: for every representative `d` of a generalized isomorphism `f` and branched `Θ`, `Θ'`,
`(Td)_* TΘ = T(d_*Θ)` and `(Td)^* TΘ' = T(d^*Θ')` on the tangent diagram `Td`, **without** any
further hypothesis.

* `A ⇒ B` fails: every identity of `A` (`tangentTheta_pushforwardTheta`,
  `tangentTheta_pullbackTheta`, `theorem_11_3_7_push/pull`, also `tangentValue_*`,
  `tangentTheta_tangentMapOn`) assumes `HasIndependentTangentSums` (Theorem 9.2.1 (1)'s
  independence of `∑ σᵢ T_xMᵢ` from the local branching structure), which the project proves only
  under extra hypotheses; `TΘ` itself (`tangentTheta`, through `tangentValue`) is computed on a
  chosen structure, so without the independence the two sides need not be comparable.  With the
  independence added to `B` (`BInd`, implied by `B`), `A ⇒ BInd` holds (`A_to_BInd`): the
  tangent diagram's push-forward is by definition `(TΦ)_* (TF)^*`, and `A`'s equivalence-level
  `tangentTheta_pullbackTheta`, `tangentTheta_pushforwardTheta`,
  `hasIndependentTangentSums_pullbackTheta` apply to the legs of `d` (`theorem_10_3_10` makes `Φ`
  an equivalence; non-item `isBranchedEpSubgroupoid_pullbackTheta`).
* `B ⇒ A` fails (`A` has content `B` lacks): `B` gives `theorem_11_3_7_push/pull`
  (`B_to_A_core`, on `rep f`, via a local copy of the two-line `tangentFunctor_map_eq` and the
  non-item `pushTheta_homMk`, `pullTheta_homMk`), but `A` also contains the transport of the
  independence itself (`hasIndependentTangentSums_push/pullforwardTheta`, `EPLoc.…_push/pullTheta`,
  `tangentSum_eq_of_isScDiffeoOn`), the local lemmas for arbitrary sc-diffeomorphisms
  (`submanifoldTangent_image_of_isScDiffeoOn`, `chartVec_tangentMapOn_of_isScDiffeoOn`,
  `tangentSum_mapDiffeo`, `tangentTheta_tangentMapOn`), the formulas for `T_Θ`
  (`tangentValue_push/pullbackTheta`), the equivalence-level identities for ep-functors and
  `tangentFunctor_map_eq`; none is stated in `B`.
-/

namespace RoundTrip.V11_23
open Polyfold Polyfold.EPLocalization CategoryTheory

/-- The project's statement (universes matched to `B`'s universe `1`, see above). -/
def A : Prop :=
  type_of% @Polyfold.MPolyfold.submanifoldTangent_image_of_isScDiffeoOn.{1, 1} ∧
  type_of% @Polyfold.MPolyfold.chartVec_tangentMapOn_of_isScDiffeoOn.{1, 1} ∧
  type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.tangentSum_mapDiffeo.{1} ∧
  type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.tangentSum_eq_of_isScDiffeoOn.{1} ∧
  type_of% @Polyfold.EpGroupoid.tangentTheta_tangentMapOn.{1} ∧
  type_of% @Polyfold.EpFunctor.hasIndependentTangentSums_pushforwardTheta.{1} ∧
  type_of% @Polyfold.EpFunctor.hasIndependentTangentSums_pullbackTheta.{1} ∧
  type_of% @Polyfold.EpFunctor.tangentValue_pushforwardTheta.{1} ∧
  type_of% @Polyfold.EpFunctor.tangentValue_pullbackTheta.{1} ∧
  type_of% @Polyfold.EpFunctor.tangentTheta_pushforwardTheta.{1} ∧
  type_of% @Polyfold.EpFunctor.tangentTheta_pullbackTheta.{1} ∧
  type_of% @Polyfold.EPLocalization.EPLoc.hasIndependentTangentSums_pushTheta.{1} ∧
  type_of% @Polyfold.EPLocalization.EPLoc.hasIndependentTangentSums_pullTheta.{1} ∧
  type_of% @Polyfold.EPLocalization.EPLoc.tangentFunctor_map_eq.{0} ∧
  type_of% @Polyfold.EPLocalization.EPLoc.theorem_11_3_7_push.{0} ∧
  type_of% @Polyfold.EPLocalization.EPLoc.theorem_11_3_7_pull.{0}

theorem A_holds : A :=
  ⟨@MPolyfold.submanifoldTangent_image_of_isScDiffeoOn,
    @MPolyfold.chartVec_tangentMapOn_of_isScDiffeoOn,
    @EpGroupoid.LocalBranchingStructure.tangentSum_mapDiffeo,
    @EpGroupoid.LocalBranchingStructure.tangentSum_eq_of_isScDiffeoOn,
    @EpGroupoid.tangentTheta_tangentMapOn,
    @EpFunctor.hasIndependentTangentSums_pushforwardTheta,
    @EpFunctor.hasIndependentTangentSums_pullbackTheta,
    @EpFunctor.tangentValue_pushforwardTheta, @EpFunctor.tangentValue_pullbackTheta,
    @EpFunctor.tangentTheta_pushforwardTheta, @EpFunctor.tangentTheta_pullbackTheta,
    @EPLoc.hasIndependentTangentSums_pushTheta, @EPLoc.hasIndependentTangentSums_pullTheta,
    @EPLoc.tangentFunctor_map_eq, @EPLoc.theorem_11_3_7_push, @EPLoc.theorem_11_3_7_pull⟩

/-- `B` with Theorem 9.2.1's independence `HasIndependentTangentSums` added to the hypotheses. -/
def BInd : Prop :=
  ∀ (X Y : EP.{1}) (f : EPLoc.of X ⟶ EPLoc.of Y), EPLoc.IsGeneralizedIso f →
    ∀ d : Diagram X Y, EPLoc.homMk d = f →
      (∀ Θ : X.Obj → ℚ, X.X.IsBranchedEpSubgroupoid Θ → X.X.HasIndependentTangentSums Θ →
        (Diagram.tangent.{0} d).pushTheta (X.X.tangentTheta Θ) =
          Y.X.tangentTheta (d.pushTheta Θ)) ∧
      (∀ Θ' : Y.Obj → ℚ, Y.X.IsBranchedEpSubgroupoid Θ' → Y.X.HasIndependentTangentSums Θ' →
        (Diagram.tangent.{0} d).pullTheta (Y.X.tangentTheta Θ') =
          X.X.tangentTheta (d.pullTheta Θ'))

theorem B_to_BInd (hB : B) : BInd := fun X Y f hf d hd =>
  ⟨fun Θ hΘ _ => (hB X Y f hf d hd).1 Θ hΘ, fun Θ' hΘ' _ => (hB X Y f hf d hd).2 Θ' hΘ'⟩

/-- **`A ⇒ BInd`**: `A`'s equivalence-level identities on the two legs of the tangent diagram. -/
theorem A_to_BInd (hA : A) : BInd := by
  obtain ⟨-, -, -, -, -, -, hind7, -, -, hT10, hT11, -, -, -, -, -⟩ := hA
  intro X Y f hf d hd
  have hΦ : d.Φ.IsEquivalence := (EPLoc.theorem_10_3_10 d).1.1 (hd ▸ hf)
  have hF := d.isEquivalence_F
  refine ⟨fun Θ hΘ hind => ?_, fun Θ' hΘ' hind' => ?_⟩
  · show d.Φ.tangent.pushforwardTheta (d.F.tangent.pullbackTheta (X.X.tangentTheta Θ)) =
      Y.X.tangentTheta (d.Φ.pushforwardTheta (d.F.pullbackTheta Θ))
    rw [hT11 hF hΘ hind,
      hT10 hΦ (EpFunctor.isBranchedEpSubgroupoid_pullbackTheta hF hΘ) (hind7 hF hind)]
  · show d.F.tangent.pushforwardTheta (d.Φ.tangent.pullbackTheta (Y.X.tangentTheta Θ')) =
      X.X.tangentTheta (d.F.pushforwardTheta (d.Φ.pullbackTheta Θ'))
    rw [hT11 hΦ hΘ' hind',
      hT10 hF (EpFunctor.isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ') (hind7 hΦ hind')]

/-- A local copy of the (two-line) `tangentFunctor_map_eq`. -/
theorem tangentFunctor_map_eq' {X Y : EP.{1}} (f : EPLoc.of X ⟶ EPLoc.of Y) :
    EPLoc.tangentFunctor.{0}.map f = EPLoc.homMk (EPLoc.rep f).tangent := by
  conv_lhs => rw [← EPLoc.homMk_rep f]
  rfl

/-- What `B` gives: `theorem_11_3_7_push`, `theorem_11_3_7_pull`. -/
theorem B_to_A_core (hB : B) :
    type_of% @Polyfold.EPLocalization.EPLoc.theorem_11_3_7_push.{0} ∧
    type_of% @Polyfold.EPLocalization.EPLoc.theorem_11_3_7_pull.{0} := by
  refine ⟨fun {X Y f} hf {Θ} hΘ hind => ?_, fun {X Y f} hf {Θ'} hΘ' hind' => ?_⟩
  · have hΦ := EPLoc.isEquivalence_rep_Φ hf
    have h := (hB X Y f hf (EPLoc.rep f) (EPLoc.homMk_rep f)).1 Θ hΘ
    rw [tangentFunctor_map_eq' f, EPLoc.pushTheta_homMk (X := X.tangent) (Y := Y.tangent)
      (EPLoc.rep f).tangent (EpFunctor.theorem_10_1_7 hΦ)
      (X.X.isFunctorial_tangentTheta hΘ hind)]
    exact h
  · have h := (hB X Y f hf (EPLoc.rep f) (EPLoc.homMk_rep f)).2 Θ' hΘ'
    rw [tangentFunctor_map_eq' f, EPLoc.pullTheta_homMk (X := X.tangent) (Y := Y.tangent)
      (EPLoc.rep f).tangent (Y.X.isFunctorial_tangentTheta hΘ' hind')]
    exact h

#rt_check RoundTrip.V11_23.A_to_BInd [
  Polyfold.MPolyfold.submanifoldTangent_image_of_isScDiffeoOn,
  Polyfold.MPolyfold.chartVec_tangentMapOn_of_isScDiffeoOn,
  Polyfold.EpGroupoid.LocalBranchingStructure.tangentSum_mapDiffeo,
  Polyfold.EpGroupoid.LocalBranchingStructure.tangentSum_eq_of_isScDiffeoOn,
  Polyfold.EpGroupoid.tangentTheta_tangentMapOn,
  Polyfold.EpFunctor.hasIndependentTangentSums_pushforwardTheta,
  Polyfold.EpFunctor.hasIndependentTangentSums_pullbackTheta,
  Polyfold.EpFunctor.tangentValue_pushforwardTheta, Polyfold.EpFunctor.tangentValue_pullbackTheta,
  Polyfold.EpFunctor.tangentTheta_pushforwardTheta, Polyfold.EpFunctor.tangentTheta_pullbackTheta,
  Polyfold.EPLocalization.EPLoc.hasIndependentTangentSums_pushTheta,
  Polyfold.EPLocalization.EPLoc.hasIndependentTangentSums_pullTheta,
  Polyfold.EPLocalization.EPLoc.tangentFunctor_map_eq,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_7_push,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_7_pull]
#rt_check RoundTrip.V11_23.B_to_A_core [
  Polyfold.MPolyfold.submanifoldTangent_image_of_isScDiffeoOn,
  Polyfold.MPolyfold.chartVec_tangentMapOn_of_isScDiffeoOn,
  Polyfold.EpGroupoid.LocalBranchingStructure.tangentSum_mapDiffeo,
  Polyfold.EpGroupoid.LocalBranchingStructure.tangentSum_eq_of_isScDiffeoOn,
  Polyfold.EpGroupoid.tangentTheta_tangentMapOn,
  Polyfold.EpFunctor.hasIndependentTangentSums_pushforwardTheta,
  Polyfold.EpFunctor.hasIndependentTangentSums_pullbackTheta,
  Polyfold.EpFunctor.tangentValue_pushforwardTheta, Polyfold.EpFunctor.tangentValue_pullbackTheta,
  Polyfold.EpFunctor.tangentTheta_pushforwardTheta, Polyfold.EpFunctor.tangentTheta_pullbackTheta,
  Polyfold.EPLocalization.EPLoc.hasIndependentTangentSums_pushTheta,
  Polyfold.EPLocalization.EPLoc.hasIndependentTangentSums_pullTheta,
  Polyfold.EPLocalization.EPLoc.tangentFunctor_map_eq,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_7_push,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_7_pull]
#rt_overlap RoundTrip.V11_23.A_to_BInd [
  Polyfold.MPolyfold.submanifoldTangent_image_of_isScDiffeoOn,
  Polyfold.MPolyfold.chartVec_tangentMapOn_of_isScDiffeoOn,
  Polyfold.EpGroupoid.LocalBranchingStructure.tangentSum_mapDiffeo,
  Polyfold.EpGroupoid.LocalBranchingStructure.tangentSum_eq_of_isScDiffeoOn,
  Polyfold.EpGroupoid.tangentTheta_tangentMapOn,
  Polyfold.EpFunctor.hasIndependentTangentSums_pushforwardTheta,
  Polyfold.EpFunctor.hasIndependentTangentSums_pullbackTheta,
  Polyfold.EpFunctor.tangentValue_pushforwardTheta, Polyfold.EpFunctor.tangentValue_pullbackTheta,
  Polyfold.EpFunctor.tangentTheta_pushforwardTheta, Polyfold.EpFunctor.tangentTheta_pullbackTheta,
  Polyfold.EPLocalization.EPLoc.hasIndependentTangentSums_pushTheta,
  Polyfold.EPLocalization.EPLoc.hasIndependentTangentSums_pullTheta,
  Polyfold.EPLocalization.EPLoc.tangentFunctor_map_eq,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_7_push,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_7_pull]

end RoundTrip.V11_23
