import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V11_6

/-! Round trip for V11_6 (2021 Proposition 11.1.6, pp. 524–525; 2017: Proposition 11.2, p. 378,
the part on `[d]_*`).

The item lists five theorems; `A` is the conjunction of their types, universes at `0` (`B`
lives in `EP.{0}`): `EPLoc.proposition_11_1_6` (for a generalized isomorphism `f`: `faceMap f`,
`θ ↦ |f|(θ)`, is a bijection of the faces of `|X|` onto those of `|Y|` with inverse
`faceComap f`; `Y_{f_*θ} = π⁻¹(|f|(θ))`; `|f|` restricts to a homeomorphism `θ → f_*θ`),
`isOrbitFace_faceMap`, `isOrbitFace_faceComap`, `faceComap_faceMap`, `faceMap_faceComap`.  None
of them assumes `X`, `Y` tame or face structured.

`B`: for tame face structured `X`, `Y` and an isomorphism `f`, every representative `d` of `f`
gives a bijection `[d]_* = Ψ_* ∘ Φ^*` of the faces of `X` (object sets `X_θ`) onto those of `Y`,
independent of `d`.

* `A_to_B` (the face-structured hypotheses are not used): for `homMk d = f`,
  `[d]_*(X_θ) = Y_{f_*θ}` for every `θ` (`dPushB_faceObj`: `Ψ_*` is the saturation of the image,
  then the project's `preimage_faceObj`, `saturation_image_faceObj`, `faceMap_homMk`, none of
  them an item theorem here); so `[d]_*` does not depend on `d`, and it is a bijection of faces by
  `A`'s `isOrbitFace_faceMap`, `isOrbitFace_faceComap`, `faceComap_faceMap`, `faceMap_faceComap`
  (and `π⁻¹` injective).
* `B_to_A`: `B` only speaks about face structured `X`, `Y`, while `A` holds for all `X`, `Y`; `A`
  is re-proved outright from non-item project lemmas (`EPLoc.isHomeomorph_orbitMap`,
  `EPLoc.degIndexOrbit_orbitMap`, Chapter 2/7's `isFaceIn_univ_image`,
  `exists_isFaceIn_univ_preimage`).  The hypothesis is not used: this direction is vacuous. -/

namespace RoundTrip.V11_6
open Polyfold CategoryTheory Set TameBoundary
open Polyfold.EPLocalization

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EPLocalization.EPLoc.proposition_11_1_6.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.isOrbitFace_faceMap.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.isOrbitFace_faceComap.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.faceComap_faceMap.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.faceMap_faceComap.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EPLocalization.EPLoc.proposition_11_1_6.{0},
    @Polyfold.EPLocalization.EPLoc.isOrbitFace_faceMap.{0},
    @Polyfold.EPLocalization.EPLoc.isOrbitFace_faceComap.{0},
    @Polyfold.EPLocalization.EPLoc.faceComap_faceMap.{0},
    @Polyfold.EPLocalization.EPLoc.faceMap_faceComap.{0}⟩

/-! ### Glue -/

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

theorem isEpFace_iff_B (X : EpGroupoid Obj Mor) (A : Set Obj) :
    IsEpFaceB X A ↔ ∃ θ, X.IsOrbitFace θ ∧ A = X.faceObj θ :=
  exists_congr fun θ => and_congr_left' (isOrbitFace_iff_B X θ).symm

end

/-- `Ψ_*(B) = {y | ∃ b ∈ B, Ψ(b) ≅ y}` is the saturation of `Ψ(B)`. -/
theorem pushObjB_eq {X Y : EP.{0}} (Φ : EpFunctor X.X Y.X) (S : Set X.Obj) :
    pushObjB Φ S = Y.X.saturation (Φ.obj '' S) := by
  ext y
  constructor
  · rintro ⟨a, ha, ψ, hs, ht⟩
    exact ⟨Φ.obj a, ⟨a, ha, rfl⟩, Y.X.π_eq_π_iff.2 ⟨ψ, hs, ht⟩⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, h⟩
    obtain ⟨ψ, hs, ht⟩ := Y.X.π_eq_π_iff.1 h
    exact ⟨a, ha, ψ, hs, ht⟩

/-- `[d]_*(X_θ) = Y_{[d]_*θ}`. -/
theorem dPushB_faceObj {X Y : EP.{0}} (d : Diagram X Y) (θ : Set X.X.OrbitSpace) :
    dPushB d (X.X.faceObj θ) = Y.X.faceObj (EPLoc.faceMap (EPLoc.homMk d) θ) := by
  rw [dPushB, pushObjB_eq, EpFunctor.preimage_faceObj, EpFunctor.saturation_image_faceObj,
    EPLoc.faceMap_homMk]

theorem A_to_B : A → B := by
  rintro ⟨-, hmap, hcomap, hcf, hfc⟩ X Y _ _ f hf
  have hg := (EPLoc.isGeneralizedIso_iff_isIso f).2 hf
  have hd : ∀ d : Diagram X Y, EPLoc.homMk d = f → ∀ θ,
      dPushB d (X.X.faceObj θ) = Y.X.faceObj (EPLoc.faceMap f θ) := by
    rintro d rfl θ
    exact dPushB_faceObj d θ
  refine ⟨fun d hdf => ⟨?_, ?_, ?_⟩, fun d d' hdf hdf' A hA => ?_⟩
  · intro A hA
    obtain ⟨θ, hθ, rfl⟩ := (isEpFace_iff_B X.X A).1 hA
    rw [mem_ofPred_eq, hd d hdf θ, isEpFace_iff_B]
    exact ⟨_, hmap hg hθ, rfl⟩
  · intro A₁ hA₁ A₂ hA₂ h
    obtain ⟨θ₁, -, rfl⟩ := (isEpFace_iff_B X.X A₁).1 hA₁
    obtain ⟨θ₂, -, rfl⟩ := (isEpFace_iff_B X.X A₂).1 hA₂
    rw [hd d hdf, hd d hdf] at h
    have h' : EPLoc.faceMap f θ₁ = EPLoc.faceMap f θ₂ :=
      Set.preimage_injective.2 Y.X.surjective_π h
    rw [← hcf hg θ₁, h', hcf hg θ₂]
  · intro A' hA'
    obtain ⟨θ', hθ', rfl⟩ := (isEpFace_iff_B Y.X A').1 hA'
    refine ⟨X.X.faceObj (EPLoc.faceComap f θ'), (isEpFace_iff_B X.X _).2
      ⟨_, hcomap hg hθ', rfl⟩, ?_⟩
    rw [hd d hdf, hfc hg θ']
  · obtain ⟨θ, -, rfl⟩ := (isEpFace_iff_B X.X A).1 hA
    rw [hd d hdf, hd d' hdf']

/-- `B → A`, vacuous: `A` re-proved outright from non-item project lemmas. -/
theorem B_to_A : B → A := by
  intro _
  have hmap : ∀ {X Y : EP.{0}} {f : EPLoc.of X ⟶ EPLoc.of Y}, EPLoc.IsGeneralizedIso f →
      ∀ {θ}, X.X.IsOrbitFace θ → Y.X.IsOrbitFace (EPLoc.faceMap f θ) := fun hf _ hθ =>
    EpGroupoid.isOrbitFace_iff_isFaceIn.2 (isFaceIn_univ_image (EPLoc.isHomeomorph_orbitMap hf)
      (EPLoc.degIndexOrbit_orbitMap hf) (EpGroupoid.isOrbitFace_iff_isFaceIn.1 hθ))
  have hcomap : ∀ {X Y : EP.{0}} {f : EPLoc.of X ⟶ EPLoc.of Y}, EPLoc.IsGeneralizedIso f →
      ∀ {θ'}, Y.X.IsOrbitFace θ' → X.X.IsOrbitFace (EPLoc.faceComap f θ') := fun hf _ hθ' =>
    EpGroupoid.isOrbitFace_iff_isFaceIn.2 (exists_isFaceIn_univ_preimage
      (EPLoc.isHomeomorph_orbitMap hf) (EPLoc.degIndexOrbit_orbitMap hf)
      (EpGroupoid.isOrbitFace_iff_isFaceIn.1 hθ'))
  have hcf : ∀ {X Y : EP.{0}} {f : EPLoc.of X ⟶ EPLoc.of Y}, EPLoc.IsGeneralizedIso f →
      ∀ θ, EPLoc.faceComap f (EPLoc.faceMap f θ) = θ := fun hf θ =>
    (EPLoc.isHomeomorph_orbitMap hf).injective.preimage_image θ
  have hfc : ∀ {X Y : EP.{0}} {f : EPLoc.of X ⟶ EPLoc.of Y}, EPLoc.IsGeneralizedIso f →
      ∀ θ', EPLoc.faceMap f (EPLoc.faceComap f θ') = θ' := fun hf θ' =>
    (EPLoc.isHomeomorph_orbitMap hf).surjective.image_preimage θ'
  refine ⟨fun {X Y f} hf => ?_, hmap, hcomap, hcf, hfc⟩
  have h₃ : InvOn (EPLoc.faceComap f) (EPLoc.faceMap f) {θ | X.X.IsOrbitFace θ}
      {θ' | Y.X.IsOrbitFace θ'} :=
    ⟨fun θ _ => hcf hf θ, fun θ' _ => hfc hf θ'⟩
  exact ⟨h₃.bijOn (fun θ hθ => hmap hf hθ) (fun θ' hθ' => hcomap hf hθ'), h₃, fun _ => rfl,
    fun θ => ⟨mapsTo_image _ θ, Homeomorph.isHomeomorph _⟩⟩

#rt_check RoundTrip.V11_6.A_to_B [Polyfold.EPLocalization.EPLoc.proposition_11_1_6,
  Polyfold.EPLocalization.EPLoc.isOrbitFace_faceMap,
  Polyfold.EPLocalization.EPLoc.isOrbitFace_faceComap,
  Polyfold.EPLocalization.EPLoc.faceComap_faceMap,
  Polyfold.EPLocalization.EPLoc.faceMap_faceComap]
#rt_check RoundTrip.V11_6.B_to_A [Polyfold.EPLocalization.EPLoc.proposition_11_1_6,
  Polyfold.EPLocalization.EPLoc.isOrbitFace_faceMap,
  Polyfold.EPLocalization.EPLoc.isOrbitFace_faceComap,
  Polyfold.EPLocalization.EPLoc.faceComap_faceMap,
  Polyfold.EPLocalization.EPLoc.faceMap_faceComap]
#rt_overlap RoundTrip.V11_6.B_to_A [Polyfold.EPLocalization.EPLoc.proposition_11_1_6,
  Polyfold.EPLocalization.EPLoc.isOrbitFace_faceMap,
  Polyfold.EPLocalization.EPLoc.isOrbitFace_faceComap,
  Polyfold.EPLocalization.EPLoc.faceComap_faceMap,
  Polyfold.EPLocalization.EPLoc.faceMap_faceComap]
#rt_overlap RoundTrip.V11_6.A_to_B [Polyfold.EPLocalization.EPLoc.proposition_11_1_6,
  Polyfold.EPLocalization.EPLoc.isOrbitFace_faceMap,
  Polyfold.EPLocalization.EPLoc.isOrbitFace_faceComap,
  Polyfold.EPLocalization.EPLoc.faceComap_faceMap,
  Polyfold.EPLocalization.EPLoc.faceMap_faceComap]

end RoundTrip.V11_6
