import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_7

/-! Round trip for V10_7 (2021 Theorem 10.1.7, p. 465; 2017: Theorem 10.1, p. 337: the tangent
of an equivalence is an equivalence).

The item lists the definition `EpFunctor.tangent` (vocabulary) and the theorem
`EpFunctor.theorem_10_1_7`; `A` is its type with both universes at `0`:
`∀ F : EpFunctor X Y, F.IsEquivalence → F.tangent.IsEquivalence` (`F.tangent` lives in `Type 1`).

`B` restates the same theorem with its own notion `IsEquivB` of Definition 10.1.1 (full and
faithful in terms of `src`, `tgt`, `mor`; a homeomorphism of `Quot`-orbit spaces extending
`|x| ↦ |F x|`; a local sc-diffeomorphism on objects), and pins down `TX`, `TF` by five equations
(object/morphism M-polyfolds, `Ts`, `Tt`, `TΦ`, `T𝚽`).

* Glue: `isEquivB_iff` (universe polymorphic, used at universes `0` and `1`):
  `IsEquivB F ↔ F.IsEquivalence`, from `GroupoidFunctor.full_iff`, `faithful_iff` and the fact
  that B's `Quot (IsoRelB G)` with its quotient topology is definitionally the project's
  `G.OrbitSpace` (`Quotient G.orbitSetoid`) with its quotient topology.
* `A_to_B`: the five equations hold by `rfl` (the definitions of `tangentEpGroupoid`,
  `tangentGroupoidStr`, `tSrc`, `tTgt`, `EpFunctor.tangent`); the implication is `A` through
  `isEquivB_iff` on both sides.
* `B_to_A`: the implication of `B` through `isEquivB_iff`.
-/

namespace RoundTrip.V10_7
open Polyfold

universe u v

section Glue

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']

/-- B's Definition 10.1.1 is the project's `EpFunctor.IsEquivalence`. -/
theorem isEquivB_iff {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (F : EpFunctor X Y) :
    IsEquivB F ↔ F.IsEquivalence := by
  constructor
  · rintro ⟨⟨hfaith, hfull⟩, ⟨e, he⟩, hloc⟩
    have hfun : (fun q : X.OrbitSpace => (e q : Y.OrbitSpace)) = F.orbitMap := by
      funext q
      induction q using Quot.ind with | mk x => exact he x
    refine ⟨(GroupoidFunctor.full_iff _).2 hfull, (GroupoidFunctor.faithful_iff _).2 hfaith,
      ?_, hloc⟩
    rw [← hfun]
    exact e.isHomeomorph
  · intro h
    exact ⟨⟨(GroupoidFunctor.faithful_iff _).1 h.faithful, (GroupoidFunctor.full_iff _).1 h.full⟩,
      ⟨h.isHomeomorph_orbitMap.homeomorph, fun _ => rfl⟩, h.isLocalScDiffeo_obj⟩

end Glue

/-- The project's statement (universes at `0`). -/
def A : Prop := type_of% @Polyfold.EpFunctor.theorem_10_1_7.{0, 0}

theorem A_holds : A := @Polyfold.EpFunctor.theorem_10_1_7.{0, 0}

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F
  refine ⟨rfl, rfl, ⟨X.isScSmoothMap_src, X.isScSmoothMap_tgt, rfl, rfl⟩, rfl, rfl, ?_⟩
  intro hF
  exact (isEquivB_iff _).2 (hA ((isEquivB_iff F).1 hF))

theorem B_to_A : B → A := by
  intro hB Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F hF
  exact (isEquivB_iff _).1
    ((hB Obj Mor Obj' Mor' X Y F).2.2.2.2.2 ((isEquivB_iff F).2 hF))

#rt_check RoundTrip.V10_7.A_to_B [Polyfold.EpFunctor.theorem_10_1_7]
#rt_check RoundTrip.V10_7.B_to_A [Polyfold.EpFunctor.theorem_10_1_7]
#rt_overlap RoundTrip.V10_7.B_to_A [Polyfold.EpFunctor.theorem_10_1_7]

end RoundTrip.V10_7
