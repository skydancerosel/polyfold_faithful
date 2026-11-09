import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V11_7

/-! Round trip for V11_7 (Remark 11.1.7 of the 2021 text, p. 525; 2017: Remark 11.2: being tame
face structured is invariant under generalized isomorphisms).

`A` is the conjunction of the types of the four listed theorems, universes at `0`:
`EPLoc.remark_11_1_7` (for a generalized isomorphism `f : X → Y`, `X` is face structured iff `Y`
is; the project's `IsEpFaceStructured` includes tameness), and the invariance of tameness alone
along an equivalence `F : X → Y`: `isTame_of_isTame_left` (`X` tame ⇒ `Y` tame),
`isTame_of_isTame` (Chapter 10, `Y` tame ⇒ `X` tame), `isTame_iff`.

`B`: for `f` an isomorphism of `EP(E⁻¹)` (`IsIso f`), `FaceStructuredB X ↔ FaceStructuredB Y`.

* Bridge: `faceStructuredB_iff` — `B`'s `FaceStructuredB` is the project's `IsEpFaceStructured`
  (the index `z.out ↦ d_X` is `degIndexOrbit`; `B`'s faces `closure (val '' connectedComponent s)`
  are `closure (connectedComponentIn {d = 1} z)` by Mathlib's `connectedComponentIn_eq_image`);
  `IsIso f ↔ IsGeneralizedIso f` is the non-item `isGeneralizedIso_iff_isIso`.
* `A_to_B`: the bridge and `remark_11_1_7`.
* `B_to_A`: `remark_11_1_7` from `B` and the bridge.  The three tameness conjuncts (for arbitrary
  ep-groupoids, tame but not necessarily face structured) are not consequences of `B`; they are
  re-proved outright (`isTame_of_isTame'`: `F` is a local sc-diffeomorphism on objects;
  `isTame_of_isTame_left'`: the project's weak-fibred-product proof, copied, with the banned
  `isTame_of_isTame` replaced by `isTame_of_isTame'`). -/

namespace RoundTrip.V11_7
open Polyfold CategoryTheory
open Polyfold.EPLocalization

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EPLocalization.EPLoc.remark_11_1_7.{0}) ∧
  (type_of% @Polyfold.EpFunctor.IsEquivalence.isTame_of_isTame_left.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsEquivalence.isTame_iff.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsEquivalence.isTame_of_isTame.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.EPLocalization.EPLoc.remark_11_1_7.{0},
    @Polyfold.EpFunctor.IsEquivalence.isTame_of_isTame_left.{0, 0},
    @Polyfold.EpFunctor.IsEquivalence.isTame_iff.{0, 0},
    @Polyfold.EpFunctor.IsEquivalence.isTame_of_isTame.{0, 0}⟩

/-! ### The bridge: `B`'s face structure is the project's -/

section Bridge

variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

theorem degOrbB_eq (X : EpGroupoid Obj Mor) (z : X.OrbitSpace) :
    degOrbB X z = X.degIndexOrbit z := by
  unfold degOrbB
  conv_rhs => rw [← Quotient.out_eq z]
  rfl

theorem isOrbitFaceB_iff (X : EpGroupoid Obj Mor) (θ : Set X.OrbitSpace) :
    IsOrbitFaceB X θ ↔ X.IsOrbitFace θ := by
  have hd : degOrbB X = X.degIndexOrbit := funext (degOrbB_eq X)
  unfold IsOrbitFaceB EpGroupoid.IsOrbitFace
  rw [hd]
  constructor
  · rintro ⟨⟨z, hz⟩, rfl⟩
    exact ⟨z, hz, by rw [connectedComponentIn_eq_image (F := {w | X.degIndexOrbit w = 1}) hz]; rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, by rw [connectedComponentIn_eq_image (F := {w | X.degIndexOrbit w = 1}) hz]; rfl⟩

theorem faceStructuredB_iff (X : EpGroupoid Obj Mor) :
    FaceStructuredB X ↔ X.IsEpFaceStructured := by
  unfold FaceStructuredB EpGroupoid.IsEpFaceStructured
  refine and_congr Iff.rfl (forall_congr' fun z => ?_)
  have hset : {θ | IsOrbitFaceB X θ ∧ z ∈ θ} = X.orbitFacesThrough z :=
    Set.ext fun θ => and_congr_left' (isOrbitFaceB_iff X θ)
  rw [hset, degOrbB_eq]

end Bridge

theorem A_to_B : A → B := by
  rintro ⟨h, -, -, -⟩ X Y f hf
  rw [faceStructuredB_iff, faceStructuredB_iff]
  exact h ((EPLoc.isGeneralizedIso_iff_isIso f).2 hf)

/-! ### Tameness along equivalences, re-proved (not a consequence of `B`) -/

section Tame

universe u v

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {F : EpFunctor X Y}

theorem isTame_of_isTame' (hF : F.IsEquivalence) (hY : Y.IsTame) : X.IsTame :=
  hF.isLocalScDiffeo_obj.isTame hY

open WeakFibredProduct in
theorem isTame_of_isTame_left' (hF : F.IsEquivalence) (hX : X.IsTame) : Y.IsTame := by
  have h : Admissible F (EpFunctor.id Y) := .of_isEquivalence_right (EpFunctor.IsEquivalence.id Y)
  have hW : (epGroupoid F (EpFunctor.id Y) h).IsTame :=
    isTame_of_isTame' (isEquivalence_projLeft (EpFunctor.IsEquivalence.id Y) h) hX
  have hsurj : Function.Surjective (projRight F (EpFunctor.id Y) h).obj := fun y => by
    obtain ⟨x, ψ, hs, ht⟩ := hF.exists_iso y
    exact ⟨WeakFibredProduct.Obj.mk F (EpFunctor.id Y) x ψ y hs ht, rfl⟩
  exact ((isEquivalence_projRight hF h).isLocalScDiffeo_obj.isTame_iff_of_surjective hsurj).1 hW

end Tame

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun {X Y f} hf => ?_, @isTame_of_isTame_left'.{0, 0},
    fun hF => ⟨isTame_of_isTame_left' hF, isTame_of_isTame' hF⟩, @isTame_of_isTame'.{0, 0}⟩
  rw [← faceStructuredB_iff, ← faceStructuredB_iff]
  exact hB X Y f ((EPLoc.isGeneralizedIso_iff_isIso f).1 hf)

#rt_check RoundTrip.V11_7.A_to_B [Polyfold.EPLocalization.EPLoc.remark_11_1_7,
  Polyfold.EpFunctor.IsEquivalence.isTame_of_isTame_left,
  Polyfold.EpFunctor.IsEquivalence.isTame_iff, Polyfold.EpFunctor.IsEquivalence.isTame_of_isTame]
#rt_check RoundTrip.V11_7.B_to_A [Polyfold.EPLocalization.EPLoc.remark_11_1_7,
  Polyfold.EpFunctor.IsEquivalence.isTame_of_isTame_left,
  Polyfold.EpFunctor.IsEquivalence.isTame_iff, Polyfold.EpFunctor.IsEquivalence.isTame_of_isTame]
#rt_overlap RoundTrip.V11_7.B_to_A [Polyfold.EPLocalization.EPLoc.remark_11_1_7,
  Polyfold.EpFunctor.IsEquivalence.isTame_of_isTame_left,
  Polyfold.EpFunctor.IsEquivalence.isTame_iff, Polyfold.EpFunctor.IsEquivalence.isTame_of_isTame]

end RoundTrip.V11_7
