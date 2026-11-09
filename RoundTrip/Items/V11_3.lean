import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V11_3

/-! Round trip for V11_3 (2021 Definition 11.1.3, p. 523; 2017: Definition 11.1, p. 377: faces
in the ep-groupoid sense, face structured and weakly face structured ep-groupoids).

The item lists the definitions `IsOrbitFace`, `faceObj`, `faceMor`, `IsEpFace`,
`orbitFacesThrough`, `IsEpFaceStructured`, `IsWeaklyFaceStructured` (vocabulary) and five
theorems; `A` is the conjunction of their types, universes at `0` (`B` quantifies over
`Obj Mor : Type`): `faceMor_eq` (`X_θ`'s morphisms are `s⁻¹(X_θ)`), `isSaturated_faceObj`,
`isOrbitFace_iff_isFaceIn` and `orbitFacesThrough_eq` (faces of `|X|` are Chapter 2's faces of
the open set `univ` for `d_{|X|}`), `isEpFaceStructured_iff`.

`B` says that the project's definitions are the blind renderings.  The content is in the
definitions, so:

* `A_to_B` is proved from the definitions (the hypothesis is not needed): `d_{|X|}(z)` equals
  `d_X(z.out)` (`Quotient.out_eq`), and `connectedComponentIn F x` is the image of the
  component of `⟨x, _⟩` in the subtype (`connectedComponentIn_eq_image`, `faceIffB`); the rest is
  `rfl` (`X.IsTame` is `X.PObj.IsTame`; `faceObj θ = π⁻¹(θ)`).
* `B_to_A`: the characterizations of faces (`isOrbitFace_iff_isFaceIn`, `orbitFacesThrough_eq`,
  `isEpFaceStructured_iff`) go through `B`'s rendering `IsOrbitFaceB` / `FaceStructuredB`;
  `faceMor_eq` goes through `B`'s `faceMorB` and `π(s φ) = π(t φ)`; `isSaturated_faceObj` (a fact
  about saturations, not a definition) is re-proved outright (`image_preimage_eq`). -/

namespace RoundTrip.V11_3
open Polyfold Set TameBoundary

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.faceMor_eq.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isSaturated_faceObj.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isOrbitFace_iff_isFaceIn.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.orbitFacesThrough_eq.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isEpFaceStructured_iff.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.faceMor_eq.{0}, @Polyfold.EpGroupoid.isSaturated_faceObj.{0},
    @Polyfold.EpGroupoid.isOrbitFace_iff_isFaceIn.{0},
    @Polyfold.EpGroupoid.orbitFacesThrough_eq.{0}, @Polyfold.EpGroupoid.isEpFaceStructured_iff.{0}⟩

/-! ### Glue -/

/-- Faces as closures of `connectedComponentIn` are faces as closures of images of components in
the subtype. -/
theorem faceIffB {S : Type} [TopologicalSpace S] (d : S → ℕ) (θ : Set S) :
    (∃ x, d x = 1 ∧ θ = closure (connectedComponentIn {y | d y = 1} x)) ↔
      ∃ s : {y // d y = 1}, θ = closure (Subtype.val '' connectedComponent s) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, by rw [connectedComponentIn_eq_image (F := {y | d y = 1}) hx]; rfl⟩
  · rintro ⟨⟨x, hx⟩, rfl⟩
    exact ⟨x, hx, by rw [connectedComponentIn_eq_image (F := {y | d y = 1}) hx]; rfl⟩

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

theorem degOrbB_eq (X : EpGroupoid Obj Mor) : degOrbB X = X.degIndexOrbit :=
  funext fun z => congrArg X.degIndexOrbit (Quotient.out_eq z)

theorem isOrbitFace_iff_B (X : EpGroupoid Obj Mor) (θ : Set X.OrbitSpace) :
    X.IsOrbitFace θ ↔ IsOrbitFaceB X θ := by
  unfold IsOrbitFaceB
  rw [degOrbB_eq]
  exact faceIffB X.degIndexOrbit θ

end

theorem A_to_B : A → B := by
  intro _ Obj Mor _ _ _ _ _ _ X
  have hface := isOrbitFace_iff_B X
  refine ⟨hface, fun θ => ⟨rfl, rfl⟩, fun A => ?_, ?_, ?_⟩
  · exact exists_congr fun θ => and_congr_left' (hface θ)
  · unfold EpGroupoid.IsEpFaceStructured FaceStructuredB EpGroupoid.orbitFacesThrough
    rw [degOrbB_eq]
    refine and_congr_right' (forall_congr' fun z => ?_)
    rw [show {θ | X.IsOrbitFace θ ∧ z ∈ θ} = {θ | IsOrbitFaceB X θ ∧ z ∈ θ} from
      Set.ext fun θ => and_congr_left' (hface θ)]
  · unfold EpGroupoid.IsWeaklyFaceStructured WeaklyFSB MPolyfold.IsFaceStructured
      IsFaceStructuredMB
    refine and_congr_right' (forall_congr' fun x => ?_)
    rw [show {F | X.PObj.IsFace F ∧ x ∈ F} = {F | IsFaceMB X.PObj F ∧ x ∈ F} from
      Set.ext fun F => and_congr_left' (faceIffB X.PObj.degIndex F)]

theorem B_to_A : B → A := by
  intro hB
  -- `B`'s faces of `|X|` are Chapter 2's faces of `univ` for `d_{|X|}`
  have hfaceIn : ∀ {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
      (θ : Set X.OrbitSpace), X.IsOrbitFace θ ↔ IsFaceIn X.degIndexOrbit univ θ := by
    intro Obj Mor _ _ _ _ _ _ X θ
    rw [(hB Obj Mor X).1 θ]
    unfold IsOrbitFaceB
    rw [degOrbB_eq, ← faceIffB]
    simp only [IsFaceIn, faceAt, univ_inter, mem_univ, true_and]
  refine ⟨?_, ?_, fun {Obj Mor} _ _ _ _ _ _ {X} {θ} => hfaceIn X θ, ?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X θ
    rw [((hB Obj Mor X).2.1 θ).2]
    ext φ
    refine ⟨And.left, fun h => ⟨h, ?_⟩⟩
    change X.π (X.tgt φ) ∈ θ
    rw [← X.π_src_eq_π_tgt φ]
    exact h
  · intro Obj Mor _ _ _ _ _ _ X θ
    change X.π ⁻¹' (X.π '' (X.π ⁻¹' θ)) = X.π ⁻¹' θ
    rw [image_preimage_eq θ X.surjective_π]
  · intro Obj Mor _ _ _ _ _ _ X z
    ext θ
    exact and_congr_left' (hfaceIn X θ)
  · intro Obj Mor _ _ _ _ _ _ X
    rw [(hB Obj Mor X).2.2.2.1]
    unfold FaceStructuredB IsFaceStructuredOpen
    rw [degOrbB_eq]
    refine and_congr_right' ⟨fun h => ⟨isOpen_univ, fun z _ => ?_⟩, fun h z => ?_⟩
    · rw [← h z]
      congr 1
      ext θ
      exact and_congr_left' ((hfaceIn X θ).symm.trans ((hB Obj Mor X).1 θ))
    · rw [← h.2 z (mem_univ z)]
      congr 1
      ext θ
      exact and_congr_left' (((hB Obj Mor X).1 θ).symm.trans (hfaceIn X θ))

#rt_check RoundTrip.V11_3.A_to_B [Polyfold.EpGroupoid.faceMor_eq,
  Polyfold.EpGroupoid.isSaturated_faceObj, Polyfold.EpGroupoid.isOrbitFace_iff_isFaceIn,
  Polyfold.EpGroupoid.orbitFacesThrough_eq, Polyfold.EpGroupoid.isEpFaceStructured_iff]
#rt_check RoundTrip.V11_3.B_to_A [Polyfold.EpGroupoid.faceMor_eq,
  Polyfold.EpGroupoid.isSaturated_faceObj, Polyfold.EpGroupoid.isOrbitFace_iff_isFaceIn,
  Polyfold.EpGroupoid.orbitFacesThrough_eq, Polyfold.EpGroupoid.isEpFaceStructured_iff]
#rt_overlap RoundTrip.V11_3.B_to_A [Polyfold.EpGroupoid.faceMor_eq,
  Polyfold.EpGroupoid.isSaturated_faceObj, Polyfold.EpGroupoid.isOrbitFace_iff_isFaceIn,
  Polyfold.EpGroupoid.orbitFacesThrough_eq, Polyfold.EpGroupoid.isEpFaceStructured_iff]

end RoundTrip.V11_3
