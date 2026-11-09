import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V11_8

/-! Round trip for V11_8 (Proposition 11.1.8 of the 2021 text, p. 526; 2017: Proposition 11.3:
generalized isomorphisms `f`, `g` of tame face-structured ep-groupoids with `|f| = |g|` have
`f_* = g_*`, and the induced maps `|F| → |f_*F|` agree).

`A` is the type of `EPLoc.proposition_11_1_8` (universe `0`): under the text's hypotheses,
`faceMap f = faceMap g`, `faceComap f = faceComap g`, and for every `θ ⊆ |X|`,
`|f|` maps `θ` into `faceMap g θ` and agrees with `|g|` on `θ`.  The project's
`faceMap f θ := |f|(θ)` and `faceComap f θ' := |f|⁻¹(θ')` are definitions (Remark 11.1.5), so
`A`'s conclusion is immediate from `|f| = |g|`; its other hypotheses are unused.

`B`: (1) for all representatives `d` of `f` and `e` of `g` and every face `X_θ` of `X` (by its
object set), `Ψ_*Φ^*(X_θ) = Ψ'_*Φ'^*(X_θ)` (`dPushB`: saturation of `Ψ(Φ⁻¹(X_θ))`); (2) on every
face `θ` of `|X|`, `|f|`, `|g|` map `θ` onto their images and agree.

* Bridge: `faceStructuredB_iff` (as in V11_7: `B`'s face structure is the project's);
  `dPushB_faceObj`: `dPushB d (X_θ) = Y_{faceMap [d] θ}`, from the non-item lemmas
  `preimage_faceObj`, `saturation_image_faceObj` and `faceMap_homMk` (Remark 11.1.5:
  `faceMap [d] = |Ψ| ∘ |Φ|⁻¹`, the identification of the project's `faceMap` with the text's
  `[d]_* = Ψ_* ∘ Φ^*`), and `π_eq_π_iff` for `B`'s saturation.
* `A_to_B`: (1) from `A`'s `faceMap f = faceMap g` and `dPushB_faceObj`; (2) from `A`'s `EqOn`.
* `B_to_A` is vacuous: `A`'s conclusion follows from its own hypothesis `|f| = |g|` (and is
  stated for every `θ`, not only faces, so `B` could not supply it).
* `B_to_A_on_faces`: `B` (1) does give `faceMap f θ = faceMap g θ` on faces `θ`
  (`Y_θ'` determines `θ'`, `π` being surjective). -/

namespace RoundTrip.V11_8
open Polyfold CategoryTheory
open Polyfold.EPLocalization

/-- The project's statement (universe `0`). -/
def A : Prop := type_of% @Polyfold.EPLocalization.EPLoc.proposition_11_1_8.{0}

theorem A_holds : A := @Polyfold.EPLocalization.EPLoc.proposition_11_1_8.{0}

/-! ### The bridge -/

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
    exact ⟨z, hz, by
      rw [connectedComponentIn_eq_image (F := {w | X.degIndexOrbit w = 1}) hz]; rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, by
      rw [connectedComponentIn_eq_image (F := {w | X.degIndexOrbit w = 1}) hz]; rfl⟩

theorem faceStructuredB_iff (X : EpGroupoid Obj Mor) :
    FaceStructuredB X ↔ X.IsEpFaceStructured := by
  unfold FaceStructuredB EpGroupoid.IsEpFaceStructured
  refine and_congr Iff.rfl (forall_congr' fun z => ?_)
  have hset : {θ | IsOrbitFaceB X θ ∧ z ∈ θ} = X.orbitFacesThrough z :=
    Set.ext fun θ => and_congr_left' (isOrbitFaceB_iff X θ)
  rw [hset, degOrbB_eq]

end Bridge

/-- `B`'s `[d]_*(X_θ)` is the project's `Y_{faceMap [d] θ}`. -/
theorem dPushB_faceObj {X Y : EP.{0}} (d : Diagram X Y) (θ : Set X.X.OrbitSpace) :
    dPushB d (X.X.faceObj θ) = Y.X.faceObj (EPLoc.faceMap (EPLoc.homMk d) θ) := by
  have hsat : ∀ S, pushObjB d.Φ S = Y.X.saturation (d.Φ.obj '' S) := by
    intro S
    ext y
    constructor
    · rintro ⟨a, ha, ψ, hs, ht⟩
      exact ⟨d.Φ.obj a, ⟨a, ha, rfl⟩, Y.X.π_eq_π_iff.2 ⟨ψ, hs, ht⟩⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, hy⟩
      obtain ⟨ψ, hs, ht⟩ := Y.X.π_eq_π_iff.1 hy
      exact ⟨a, ha, ψ, hs, ht⟩
  unfold dPushB
  rw [hsat, EpFunctor.preimage_faceObj, EpFunctor.saturation_image_faceObj,
    EPLoc.faceMap_homMk]

theorem A_to_B : A → B := by
  intro hA X Y hX hY f g hf hg h
  obtain ⟨hfg, -, hEq⟩ := hA ((EPLoc.isGeneralizedIso_iff_isIso f).2 hf)
    ((EPLoc.isGeneralizedIso_iff_isIso g).2 hg) ((faceStructuredB_iff _).1 hX)
    ((faceStructuredB_iff _).1 hY) h
  refine ⟨fun d e hd he S hS => ?_, fun θ _ =>
    ⟨Set.mapsTo_image _ θ, Set.mapsTo_image _ θ, fun z hz => (hEq θ).2 hz⟩⟩
  obtain ⟨θ, -, rfl⟩ := hS
  rw [show faceObjB X.X θ = X.X.faceObj θ from rfl, dPushB_faceObj, dPushB_faceObj, hd, he, hfg]

/-- Vacuous: `A`'s conclusion follows from its hypothesis `|f| = |g|`. -/
theorem B_to_A : B → A := by
  intro _ X Y f g _ _ _ _ h
  refine ⟨?_, ?_, fun θ => ⟨?_, fun q _ => congrFun h q⟩⟩
  · funext θ; rw [EPLoc.faceMap, EPLoc.faceMap, h]
  · funext θ; rw [EPLoc.faceComap, EPLoc.faceComap, h]
  · rw [EPLoc.faceMap, ← h]; exact Set.mapsTo_image _ θ

/-- `B` (1) gives `faceMap f θ = faceMap g θ` for the faces `θ` of `|X|`. -/
theorem B_to_A_on_faces (hB : B) {X Y : EP.{0}} {f g : EPLoc.of X ⟶ EPLoc.of Y}
    (hX : FaceStructuredB X.X) (hY : FaceStructuredB Y.X) (hf : IsIso f) (hg : IsIso g)
    (h : EPLoc.orbitMap f = EPLoc.orbitMap g) {θ : Set X.X.OrbitSpace}
    (hθ : IsOrbitFaceB X.X θ) : EPLoc.faceMap f θ = EPLoc.faceMap g θ := by
  obtain ⟨d, rfl⟩ := EPLoc.homMk_surjective f
  obtain ⟨e, rfl⟩ := EPLoc.homMk_surjective g
  have h1 := (hB X Y hX hY _ _ hf hg h).1 d e rfl rfl (faceObjB X.X θ) ⟨θ, hθ, rfl⟩
  rw [show faceObjB X.X θ = X.X.faceObj θ from rfl, dPushB_faceObj, dPushB_faceObj] at h1
  exact (Set.preimage_injective.2 Y.X.surjective_π) h1

#rt_check RoundTrip.V11_8.A_to_B [Polyfold.EPLocalization.EPLoc.proposition_11_1_8]
#rt_check RoundTrip.V11_8.B_to_A [Polyfold.EPLocalization.EPLoc.proposition_11_1_8]
#rt_check RoundTrip.V11_8.B_to_A_on_faces [Polyfold.EPLocalization.EPLoc.proposition_11_1_8]
#rt_overlap RoundTrip.V11_8.B_to_A [Polyfold.EPLocalization.EPLoc.proposition_11_1_8]
#rt_overlap RoundTrip.V11_8.A_to_B [Polyfold.EPLocalization.EPLoc.proposition_11_1_8]

end RoundTrip.V11_8
