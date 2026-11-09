import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_29

/-! Round trip for V7_29 (Definition 7.10: ep-subgroupoids).

`A` is the conjunction of the types of the listed theorems, at universe `0` (B lives in `Type`):
`EpGroupoid.isEpSubgroupoid_univ`, `isEpSubgroupoid_of_isOpen`, `isEpSubgroupoid_saturation`,
`isEpSubgroupoid_trivial`.  `EpGroupoid.IsEpSubgroupoid` is the definition (vocabulary).

B is the definitional statement "`X.IsEpSubgroupoid A` iff `A` is a sub-M-polyfold of `X.PObj`
and `π⁻¹(π(A)) = A`".  The project's structure `IsEpSubgroupoid` has exactly these two fields
(`isSubMPolyfold`, `isSaturated`), and `GroupoidStr.IsSaturated A` is literally
`π⁻¹(π(A)) = A`; so B holds outright (`B_holds`), and `A → B` does not use A.

`B → A`: the four conjuncts of A are satisfiability witnesses that the text does not state
(`univ`, saturated open sets, saturations `π⁻¹(π(U))` of open sets, every sub-M-polyfold of the
trivial ep-groupoid).  B is used only to package `IsEpSubgroupoid` from its two conditions; the
conditions themselves are proved from Part I / Chapter 7 lemmas outside the item
(`isSubMPolyfold_univ`, `isSaturated_univ`, an open set is a sub-M-polyfold with `r = id`,
Proposition 7.1 `proposition_7_1_8`, `isSaturated_trivial`). -/

namespace RoundTrip.V7_29
open Polyfold Set

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.isEpSubgroupoid_univ.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.isEpSubgroupoid_of_isOpen.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.isEpSubgroupoid_saturation.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.isEpSubgroupoid_trivial.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.isEpSubgroupoid_univ.{0}, @Polyfold.EpGroupoid.isEpSubgroupoid_of_isOpen.{0},
    @Polyfold.EpGroupoid.isEpSubgroupoid_saturation.{0},
    @Polyfold.EpGroupoid.isEpSubgroupoid_trivial.{0}⟩

/-- B outright: the project's Definition 7.10 is the text's. -/
theorem B_holds : B := fun _ _ _ _ _ _ _ _ _ _ =>
  ⟨fun h => ⟨h.isSubMPolyfold, h.isSaturated⟩, fun h => ⟨h.1, h.2⟩⟩

theorem A_to_B : A → B := fun _ => B_holds

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X
    exact (hB Obj Mor X univ).2 ⟨X.PObj.isSubMPolyfold_univ, X.isSaturated_univ⟩
  · intro Obj Mor _ _ _ _ _ _ X S hS hs
    refine (hB Obj Mor X S).2 ⟨fun a ha => ⟨S, hS, ha, id, mapsTo_id _,
      MPolyfold.isScSmoothMap_id.mono hS (subset_univ _), fun _ _ => rfl, by
        rw [image_id, inter_self]⟩, hs⟩
  · intro Obj Mor _ _ _ _ _ _ X U hU
    have hO : IsOpen (X.saturation U) := (X.proposition_7_1_8 U hU).preimage X.continuous_π
    refine (hB Obj Mor X _).2 ⟨fun a ha => ⟨_, hO, ha, id, mapsTo_id _,
      MPolyfold.isScSmoothMap_id.mono hO (subset_univ _), fun _ _ => rfl, by
        rw [image_id, inter_self]⟩, ?_⟩
    change X.π ⁻¹' (X.π '' (X.π ⁻¹' (X.π '' U))) = X.π ⁻¹' (X.π '' U)
    rw [image_preimage_eq _ X.surjective_π]
  · intro Z _ _ _ P S hS
    exact (hB Z Z (EpGroupoid.trivial P) S).2 ⟨hS, GroupoidStr.isSaturated_trivial S⟩

#rt_check RoundTrip.V7_29.A_to_B [Polyfold.EpGroupoid.isEpSubgroupoid_univ,
  Polyfold.EpGroupoid.isEpSubgroupoid_of_isOpen, Polyfold.EpGroupoid.isEpSubgroupoid_saturation,
  Polyfold.EpGroupoid.isEpSubgroupoid_trivial]
#rt_check RoundTrip.V7_29.B_to_A [Polyfold.EpGroupoid.isEpSubgroupoid_univ,
  Polyfold.EpGroupoid.isEpSubgroupoid_of_isOpen, Polyfold.EpGroupoid.isEpSubgroupoid_saturation,
  Polyfold.EpGroupoid.isEpSubgroupoid_trivial]
#rt_overlap RoundTrip.V7_29.B_to_A [Polyfold.EpGroupoid.isEpSubgroupoid_univ,
  Polyfold.EpGroupoid.isEpSubgroupoid_of_isOpen, Polyfold.EpGroupoid.isEpSubgroupoid_saturation,
  Polyfold.EpGroupoid.isEpSubgroupoid_trivial]

end RoundTrip.V7_29
