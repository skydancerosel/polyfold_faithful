import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V11_5

/-! Round trip for V11_5 (2021 Remark 11.1.5, p. 524; 2017: Remark 11.1, p. 378: bijections of
faces under equivalences and generalized isomorphisms).

The item lists the definitions `EPLoc.faceMap` (`[d]_*θ = |[d]|(θ)`), `EPLoc.faceComap`
(`[d]^*θ' = |[d]|⁻¹(θ')`) (vocabulary) and twelve theorems; `A` is the conjunction of their
types, all universes at `0` (`B` lives in `EP.{0}`): `EPLoc.remark_11_1_5` (the remark),
`EpFunctor.saturation_image_faceObj` (`Φ_*(X_θ) = Y_{|Φ|(θ)}`, any functor, any `θ`),
`EpFunctor.preimage_faceObj` (`Φ^*(Y_θ') = X_{|Φ|⁻¹(θ')}`), `IsEquivalence.bijOn_faces`
(bijection, inverse `|Φ|⁻¹`), `EPLoc.faceMap_homMk`, `EPLoc.faceComap_homMk`
(`[d]_* = Ψ_* ∘ Φ^*`, `[d]^* = Φ_* ∘ Ψ^*` on orbit sets, any diagram, any `θ`),
`EPLoc.bijOn_faceMap`, `EPLoc.isHomeomorph_orbitMap`, and four transport lemmas of Chapter 2's
faces along index-preserving homeomorphisms (`TameBoundary.isDHomeoOn_univ`,
`isFaceIn_univ_image`, `exists_isFaceIn_univ_preimage`, `isFaceStructuredOpen_univ_iff`).

* `A_to_B`: `B`'s faces of `|X|` are the project's (`isOrbitFace_iff_B`); `B`'s
  `pushObjB Φ S = {y | ∃ s ∈ S, Φ(s) ≅ y}` is the saturation of `Φ(S)` (`pushObjB_eq`); then (a)
  is `remark_11_1_5`'s first half, and (b) is `bijOn_faceMap` with the formulas
  `preimage_faceObj`, `saturation_image_faceObj`, `faceMap_homMk`, `faceComap_homMk`.
* `B_to_A`: the bijections come from `B`: `remark_11_1_5`'s two `BijOn`, `bijOn_faces` (for
  unbundled `X`, `Y`: bundle them as `EP.mk _ _ X`; its `MapsTo |Φ|⁻¹` from `B`'s surjectivity
  and injectivity of `|Φ|`), `bijOn_faceMap`.  The rest is not a consequence of `B` (`B` speaks
  of equivalences and faces only; `A`'s formulas hold for every functor, diagram and `θ`, and
  the transport lemmas are general topology) and is re-proved outright from non-item project
  lemmas (the project's proofs, copied). -/

namespace RoundTrip.V11_5
open Polyfold CategoryTheory Set TameBoundary
open Polyfold.EPLocalization

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EPLocalization.EPLoc.remark_11_1_5.{0}) ∧
  (type_of% @Polyfold.EpFunctor.saturation_image_faceObj.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.preimage_faceObj.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsEquivalence.bijOn_faces.{0, 0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.faceMap_homMk.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.faceComap_homMk.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.bijOn_faceMap.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.isHomeomorph_orbitMap.{0}) ∧
  (type_of% @Polyfold.TameBoundary.isDHomeoOn_univ.{0, 0}) ∧
  (type_of% @Polyfold.TameBoundary.isFaceIn_univ_image.{0, 0}) ∧
  (type_of% @Polyfold.TameBoundary.exists_isFaceIn_univ_preimage.{0, 0}) ∧
  (type_of% @Polyfold.TameBoundary.isFaceStructuredOpen_univ_iff.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.EPLocalization.EPLoc.remark_11_1_5.{0},
    @Polyfold.EpFunctor.saturation_image_faceObj.{0, 0},
    @Polyfold.EpFunctor.preimage_faceObj.{0, 0},
    @Polyfold.EpFunctor.IsEquivalence.bijOn_faces.{0, 0},
    @Polyfold.EPLocalization.EPLoc.faceMap_homMk.{0},
    @Polyfold.EPLocalization.EPLoc.faceComap_homMk.{0},
    @Polyfold.EPLocalization.EPLoc.bijOn_faceMap.{0},
    @Polyfold.EPLocalization.EPLoc.isHomeomorph_orbitMap.{0},
    @Polyfold.TameBoundary.isDHomeoOn_univ.{0, 0},
    @Polyfold.TameBoundary.isFaceIn_univ_image.{0, 0},
    @Polyfold.TameBoundary.exists_isFaceIn_univ_preimage.{0, 0},
    @Polyfold.TameBoundary.isFaceStructuredOpen_univ_iff.{0, 0}⟩

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
  {Obj' Mor' : Type} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']

theorem degOrbB_eq (X : EpGroupoid Obj Mor) : degOrbB X = X.degIndexOrbit :=
  funext fun z => congrArg X.degIndexOrbit (Quotient.out_eq z)

theorem isOrbitFace_iff_B (X : EpGroupoid Obj Mor) (θ : Set X.OrbitSpace) :
    X.IsOrbitFace θ ↔ IsOrbitFaceB X θ := by
  unfold IsOrbitFaceB
  rw [degOrbB_eq]
  exact faceIffB X.degIndexOrbit θ

theorem setOf_isOrbitFaceB (X : EpGroupoid Obj Mor) :
    {θ | IsOrbitFaceB X θ} = {θ | X.IsOrbitFace θ} :=
  Set.ext fun θ => (isOrbitFace_iff_B X θ).symm

/-- `Φ_*(S) = {y | ∃ s ∈ S, Φ(s) ≅ y}` is the saturation of `Φ(S)`. -/
theorem pushObjB_eq {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (Φ : EpFunctor X Y)
    (S : Set Obj) : pushObjB Φ S = Y.saturation (Φ.obj '' S) := by
  ext y
  constructor
  · rintro ⟨a, ha, ψ, hs, ht⟩
    exact ⟨Φ.obj a, ⟨a, ha, rfl⟩, Y.π_eq_π_iff.2 ⟨ψ, hs, ht⟩⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, h⟩
    obtain ⟨ψ, hs, ht⟩ := Y.π_eq_π_iff.1 h
    exact ⟨a, ha, ψ, hs, ht⟩

/-- `Φ_*(X_θ) = Y_{|Φ|(θ)}` (the project's proof of `saturation_image_faceObj`, copied). -/
theorem saturation_image_faceObj' {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}
    (Φ : EpFunctor X Y) (θ : Set X.OrbitSpace) :
    Y.saturation (Φ.obj '' X.faceObj θ) = Y.faceObj (Φ.orbitMap '' θ) := by
  change Y.π ⁻¹' (Y.π '' (Φ.obj '' (X.π ⁻¹' θ))) = Y.π ⁻¹' (Φ.orbitMap '' θ)
  congr 1
  rw [image_image]
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨X.π x, hx, GroupoidFunctor.orbitMap_π _ x⟩
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨x, rfl⟩ := X.surjective_π q
    exact ⟨x, hq, (GroupoidFunctor.orbitMap_π _ x).symm⟩

/-- `Φ^*(Y_θ') = X_{|Φ|⁻¹(θ')}` (copied). -/
theorem preimage_faceObj' {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}
    (Φ : EpFunctor X Y) (θ' : Set Y.OrbitSpace) :
    Φ.obj ⁻¹' Y.faceObj θ' = X.faceObj (Φ.orbitMap ⁻¹' θ') := by
  ext x
  change Y.π (Φ.obj x) ∈ θ' ↔ Φ.orbitMap (X.π x) ∈ θ'
  rw [GroupoidFunctor.orbitMap_π]

end

section
variable {X Y : EP.{0}}

/-- `|[d]|` is a homeomorphism for a generalized isomorphism (copied). -/
theorem isHomeomorph_orbitMap' {f : EPLoc.of X ⟶ EPLoc.of Y} (hf : EPLoc.IsGeneralizedIso f) :
    IsHomeomorph (EPLoc.orbitMap f) := by
  obtain ⟨d, rfl, hΦ⟩ := EPLoc.exists_diagram_of_isGeneralizedIso hf
  exact d.isHomeomorph_orbitMap hΦ

/-- `[d]_* = Ψ_* ∘ Φ^*` on orbit sets (copied). -/
theorem faceMap_homMk' (d : Diagram X Y) (θ : Set X.X.OrbitSpace) :
    EPLoc.faceMap (EPLoc.homMk d) θ = d.Φ.orbitMap '' (d.F.orbitMap ⁻¹' θ) := by
  rw [EPLoc.faceMap, EPLoc.orbitMap_homMk]
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨r, rfl⟩ := d.isEquivalence_F.isHomeomorph_orbitMap.surjective p
    exact ⟨r, hp, (d.orbitMap_orbitMap_F r).symm⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨_, hr, d.orbitMap_orbitMap_F r⟩

/-- `[d]^* = Φ_* ∘ Ψ^*` on orbit sets (copied). -/
theorem faceComap_homMk' (d : Diagram X Y) (θ' : Set Y.X.OrbitSpace) :
    EPLoc.faceComap (EPLoc.homMk d) θ' = d.F.orbitMap '' (d.Φ.orbitMap ⁻¹' θ') := by
  rw [EPLoc.faceComap, EPLoc.orbitMap_homMk]
  ext p
  obtain ⟨r, rfl⟩ := d.isEquivalence_F.isHomeomorph_orbitMap.surjective p
  simp only [mem_preimage, d.orbitMap_orbitMap_F,
    d.isEquivalence_F.isHomeomorph_orbitMap.injective.mem_set_image]

end

/-! ### The two directions -/

theorem A_to_B : A → B := by
  rintro ⟨hrem, hsat, hpre, -, hfm, hfc, hbij, -⟩
  refine ⟨fun X Y Φ hΦ => ?_, fun X Y f hf => ?_⟩
  · rw [setOf_isOrbitFaceB, setOf_isOrbitFaceB]
    refine ⟨((hrem (X := X) (Y := Y)).1 Φ hΦ).1, fun θ _ => ?_, fun θ' _ => hpre Φ θ'⟩
    rw [pushObjB_eq]
    exact hsat Φ θ
  · have hg := (EPLoc.isGeneralizedIso_iff_isIso f).2 hf
    rw [setOf_isOrbitFaceB, setOf_isOrbitFaceB]
    refine ⟨(hbij hg).1, ?_⟩
    rintro d rfl
    refine ⟨fun θ _ => ?_, fun θ' _ => ?_⟩
    · rw [pushObjB_eq, show faceObjB X.X θ = X.X.faceObj θ from rfl, hpre, hsat]
      exact congrArg _ (hfm d θ).symm
    · rw [pushObjB_eq, show faceObjB Y.X θ' = Y.X.faceObj θ' from rfl, hpre, hsat]
      exact congrArg _ (hfc d θ').symm

theorem B_to_A : B → A := by
  rintro ⟨hBa, hBb⟩
  -- the bijections, from `B`
  have hbijE : ∀ {A₀ B₀ : EP.{0}} (Φ : EpFunctor A₀.X B₀.X), Φ.IsEquivalence →
      BijOn (image Φ.orbitMap) {θ | A₀.X.IsOrbitFace θ} {θ' | B₀.X.IsOrbitFace θ'} := by
    intro A₀ B₀ Φ hΦ
    have h := (hBa A₀ B₀ Φ hΦ).1
    rwa [setOf_isOrbitFaceB, setOf_isOrbitFaceB] at h
  have hbijG : ∀ {X Y : EP.{0}} {f : EPLoc.of X ⟶ EPLoc.of Y}, EPLoc.IsGeneralizedIso f →
      BijOn (EPLoc.faceMap f) {θ | X.X.IsOrbitFace θ} {θ' | Y.X.IsOrbitFace θ'} := by
    intro X Y f hf
    have h := (hBb X Y f ((EPLoc.isGeneralizedIso_iff_isIso f).1 hf)).1
    rwa [setOf_isOrbitFaceB, setOf_isOrbitFaceB] at h
  have hinvG : ∀ {X Y : EP.{0}} {f : EPLoc.of X ⟶ EPLoc.of Y}, EPLoc.IsGeneralizedIso f →
      InvOn (EPLoc.faceComap f) (EPLoc.faceMap f) {θ | X.X.IsOrbitFace θ}
        {θ' | Y.X.IsOrbitFace θ'} := fun hf =>
    ⟨fun θ _ => (isHomeomorph_orbitMap' hf).injective.preimage_image θ,
      fun θ' _ => (isHomeomorph_orbitMap' hf).surjective.image_preimage θ'⟩
  refine ⟨⟨fun Φ hΦ => ⟨hbijE Φ hΦ, saturation_image_faceObj' Φ, preimage_faceObj' Φ⟩,
      fun d hΦ => ⟨faceMap_homMk' d, faceComap_homMk' d,
        hbijG ((EPLoc.theorem_10_3_10 d).1.2 hΦ), hinvG ((EPLoc.theorem_10_3_10 d).1.2 hΦ)⟩⟩,
    fun Φ θ => saturation_image_faceObj' Φ θ, fun Φ θ' => preimage_faceObj' Φ θ', ?_,
    fun d θ => faceMap_homMk' d θ, fun d θ' => faceComap_homMk' d θ', fun hf => ⟨hbijG hf, hinvG hf⟩,
    fun hf => isHomeomorph_orbitMap' hf, ?_, ?_, ?_, ?_⟩
  · -- `IsEquivalence.bijOn_faces`: bundle `X`, `Y`
    intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y Φ hΦ
    have hb : BijOn (image Φ.orbitMap) {θ | X.IsOrbitFace θ} {θ' | Y.IsOrbitFace θ'} :=
      hbijE (A₀ := EP.mk Obj Mor X) (B₀ := EP.mk Obj' Mor' Y) Φ hΦ
    have he := hΦ.isHomeomorph_orbitMap
    have h₃ : InvOn (preimage Φ.orbitMap) (image Φ.orbitMap) {θ | X.IsOrbitFace θ}
        {θ' | Y.IsOrbitFace θ'} :=
      ⟨fun θ _ => he.injective.preimage_image θ, fun θ' _ => he.surjective.image_preimage θ'⟩
    refine ⟨hb, h₃, fun θ' hθ' => ?_⟩
    obtain ⟨θ, hθ, rfl⟩ := hb.surjOn hθ'
    rw [mem_ofPred_eq, he.injective.preimage_image]
    exact hθ
  -- the transport lemmas of Chapter 2's faces (general topology; the project's proofs, copied)
  · intro S _ T _ dS dT e he hd
    exact ⟨isOpen_univ, he.continuous.continuousOn, he.injective.injOn,
      fun U hU _ => he.isOpenMap U hU, fun s _ => hd s⟩
  · intro S _ T _ dS dT e he hd θ hθ
    have h := (IsDHomeoOn.isFaceIn_image (show IsDHomeoOn dS dT e univ from
      ⟨isOpen_univ, he.continuous.continuousOn, he.injective.injOn,
        fun U hU _ => he.isOpenMap U hU, fun s _ => hd s⟩)) subset_rfl hθ
    rwa [image_univ_of_surjective he.surjective] at h
  · intro S _ T _ dS dT e he hd θ' hθ'
    have hD : IsDHomeoOn dS dT e univ := ⟨isOpen_univ, he.continuous.continuousOn,
      he.injective.injOn, fun U hU _ => he.isOpenMap U hU, fun s _ => hd s⟩
    rw [← image_univ_of_surjective he.surjective] at hθ'
    obtain ⟨θ, hθ, rfl⟩ := hD.exists_isFaceIn_of_image subset_rfl hθ'
    rwa [he.injective.preimage_image]
  · intro S _ T _ dS dT e he hd
    have hD : IsDHomeoOn dS dT e univ := ⟨isOpen_univ, he.continuous.continuousOn,
      he.injective.injOn, fun U hU _ => he.isOpenMap U hU, fun s _ => hd s⟩
    refine ⟨fun h => ?_, fun h => ⟨isOpen_univ, fun y _ => ?_⟩⟩
    · have h' := hD.isFaceStructuredOpen_image subset_rfl h
      rwa [image_univ_of_surjective he.surjective] at h'
    · have h' := hD.encard_facesThrough_image subset_rfl (mem_univ y)
      rw [image_univ_of_surjective he.surjective, h.2 _ (mem_univ _), hd] at h'
      exact h'.symm

#rt_check RoundTrip.V11_5.A_to_B [Polyfold.EPLocalization.EPLoc.remark_11_1_5,
  Polyfold.EpFunctor.saturation_image_faceObj, Polyfold.EpFunctor.preimage_faceObj,
  Polyfold.EpFunctor.IsEquivalence.bijOn_faces, Polyfold.EPLocalization.EPLoc.faceMap_homMk,
  Polyfold.EPLocalization.EPLoc.faceComap_homMk, Polyfold.EPLocalization.EPLoc.bijOn_faceMap,
  Polyfold.EPLocalization.EPLoc.isHomeomorph_orbitMap, Polyfold.TameBoundary.isDHomeoOn_univ,
  Polyfold.TameBoundary.isFaceIn_univ_image, Polyfold.TameBoundary.exists_isFaceIn_univ_preimage,
  Polyfold.TameBoundary.isFaceStructuredOpen_univ_iff]
#rt_check RoundTrip.V11_5.B_to_A [Polyfold.EPLocalization.EPLoc.remark_11_1_5,
  Polyfold.EpFunctor.saturation_image_faceObj, Polyfold.EpFunctor.preimage_faceObj,
  Polyfold.EpFunctor.IsEquivalence.bijOn_faces, Polyfold.EPLocalization.EPLoc.faceMap_homMk,
  Polyfold.EPLocalization.EPLoc.faceComap_homMk, Polyfold.EPLocalization.EPLoc.bijOn_faceMap,
  Polyfold.EPLocalization.EPLoc.isHomeomorph_orbitMap, Polyfold.TameBoundary.isDHomeoOn_univ,
  Polyfold.TameBoundary.isFaceIn_univ_image, Polyfold.TameBoundary.exists_isFaceIn_univ_preimage,
  Polyfold.TameBoundary.isFaceStructuredOpen_univ_iff]
#rt_overlap RoundTrip.V11_5.B_to_A [Polyfold.EPLocalization.EPLoc.remark_11_1_5,
  Polyfold.EpFunctor.saturation_image_faceObj, Polyfold.EpFunctor.preimage_faceObj,
  Polyfold.EpFunctor.IsEquivalence.bijOn_faces, Polyfold.EPLocalization.EPLoc.faceMap_homMk,
  Polyfold.EPLocalization.EPLoc.faceComap_homMk, Polyfold.EPLocalization.EPLoc.bijOn_faceMap,
  Polyfold.EPLocalization.EPLoc.isHomeomorph_orbitMap, Polyfold.TameBoundary.isDHomeoOn_univ,
  Polyfold.TameBoundary.isFaceIn_univ_image, Polyfold.TameBoundary.exists_isFaceIn_univ_preimage,
  Polyfold.TameBoundary.isFaceStructuredOpen_univ_iff]

end RoundTrip.V11_5
