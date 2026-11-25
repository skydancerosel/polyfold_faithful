import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_65

set_option maxSynthPendingDepth 3

/-! Round trip for V17_65 (2021 Proposition 17.3.8, p. 787: if the tame `C` is face-structured,
every face is a subpolyfold).

The item lists `quadrantConstruction` (a definition, vocabulary) and two theorems; `A` is the
conjunction of their types (`proposition_17_3_8` at universe `0`): `proposition_17_3_8` (for a
covering family `c`, `IsFaceStructuredVia c` and a face `θ` (via `c`), `π⁻¹(θ)` satisfies both
Definition 17.3.2 and Definition 17.3.1) and `quadrant_proposition_17_3_8` (the quadrant
`[0,∞)² ⊕ W` is a tame face-structured witness with a face through the corner that is a
subpolyfold in both senses).

* `A_to_B`: the second component of `proposition_17_3_8` (`B`'s `Def1` is the project's
  `IsSubpolyfold`; `B`'s extra hypothesis `S.IsTame` is already inside `IsFaceStructuredVia`).
* `B_to_A`: `B` gives the Definition 17.3.1 half (used for both conjuncts).  The
  Definition 17.3.2 half is not a consequence of Definition 17.3.1 in general (it needs
  `F(α) ≠ ∅` on the face, cf. V17_60), so it is re-proved from non-item lemmas
  (`isFaceStructuredVia_iff`, `isFaceVia_iff_isOrbitFace`, `EpGroupoid.isEpSubgroupoid_faceObj`):
  the faces of the model `X_c` are ep-subgroupoids (Ch. 11).  The witness's tameness and
  face-structure are re-proved as in the project. -/

namespace RoundTrip.V17_65
open Polyfold GCT.PolyfoldConstruction Set

def A : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_3_8.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.quadrant_proposition_17_3_8)

theorem A_holds : A :=
  ⟨@Polyfold.GCT.PolyfoldConstruction.proposition_17_3_8.{0},
    @Polyfold.GCT.PolyfoldConstruction.quadrant_proposition_17_3_8⟩

theorem A_to_B : A → B := fun hA _ S c _ hF _ hθ => (hA.1 S c hF hθ).2

/-- Definition 17.3.2 for a face (the project's argument through the model `X_c`). -/
theorem isSubpolyfoldModel_face {C : GCT.{0}} (S : C.PolyfoldConstruction) (c : S.CoveringFamily)
    (hF : S.IsFaceStructuredVia c) {θ : Set C.toGroupoidStr.OrbitSpace} (hθ : S.IsFaceVia c θ) :
    S.IsSubpolyfoldModel (C.toGroupoidStr.π ⁻¹' θ) :=
  ⟨isSaturated_π_preimage θ, c, EpGroupoid.isEpSubgroupoid_faceObj
    ((S.isFaceStructuredVia_iff hF.1 c c).1 hF) ((S.isFaceVia_iff_isOrbitFace c c θ).1 hθ)⟩

theorem B_to_main : B → type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_3_8.{0} :=
  fun hB _ S c hF _ hθ => ⟨isSubpolyfoldModel_face S c hF hθ, hB _ S c hF.1 hF _ hθ⟩

section Quadrant
open MPolyfold TameBoundaryExample

theorem B_to_quadrant (hB : B) :
    type_of% @Polyfold.GCT.PolyfoldConstruction.quadrant_proposition_17_3_8 := by
  intro W
  have hT : (quadrantConstruction W).IsTame :=
    twistConstruction_isTame _ _ (quadrantPolyfold_isTame 2 W)
  have hF : (quadrantConstruction W).IsFaceStructuredVia (quadrantFamily W) :=
    ((quadrantConstruction W).isFaceStructuredVia_iff_isFaceStructuredOpen _).2
      ⟨hT, (TameBoundary.isFaceStructuredOpen_univ_iff (quadrant_isHomeomorph_π W)
        (quadrant_degIndexVia W)).1 (isFaceStructuredOpen_quadrant isOpen_univ)⟩
  have h2 : (quadrantConstruction W).degIndexVia (quadrantFamily W)
      ((GroupoidStr.translation Unit (quadrant 2 W 0)).π (quadrantCorner W)) = 2 :=
    (quadrant_degIndexVia W _).trans (quadrantPolyfold_degIndex_zero 2 W)
  have hc := hF.2 ((GroupoidStr.translation Unit (quadrant 2 W 0)).π (quadrantCorner W))
  rw [h2] at hc
  obtain ⟨θ, hθ, hz⟩ := nonempty_of_encard_ne_zero (s := {θ | (quadrantConstruction W).IsFaceVia
    (quadrantFamily W) θ ∧
      (GroupoidStr.translation Unit (quadrant 2 W 0)).π (quadrantCorner W) ∈ θ})
    (by rw [hc]; exact two_ne_zero)
  exact ⟨hT, hF, h2, hc, θ, hθ, hz, isSubpolyfoldModel_face _ _ hF hθ,
    hB _ (quadrantConstruction W) (quadrantFamily W) hT hF θ hθ⟩

end Quadrant

theorem B_to_A : B → A := fun hB => ⟨B_to_main hB, B_to_quadrant hB⟩

#rt_check RoundTrip.V17_65.A_to_B [Polyfold.GCT.PolyfoldConstruction.proposition_17_3_8,
  Polyfold.GCT.PolyfoldConstruction.quadrant_proposition_17_3_8]
#rt_check RoundTrip.V17_65.B_to_A [Polyfold.GCT.PolyfoldConstruction.proposition_17_3_8,
  Polyfold.GCT.PolyfoldConstruction.quadrant_proposition_17_3_8]
#rt_check RoundTrip.V17_65.B_to_main [Polyfold.GCT.PolyfoldConstruction.proposition_17_3_8,
  Polyfold.GCT.PolyfoldConstruction.quadrant_proposition_17_3_8]
#rt_overlap RoundTrip.V17_65.B_to_A [Polyfold.GCT.PolyfoldConstruction.proposition_17_3_8,
  Polyfold.GCT.PolyfoldConstruction.quadrant_proposition_17_3_8]

end RoundTrip.V17_65
