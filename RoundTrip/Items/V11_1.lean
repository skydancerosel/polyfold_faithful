import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V11_1

set_option maxSynthPendingDepth 3

/-! Round trip for V11_1 (2021 Theorem 11.1.1, p. 521; 2017: Theorem 11.1, p. 375: the tangent
functor on `EP(E⁻¹)`).

The item lists the definitions `EPLoc.tangentFunctor`, `Diagram.tangent`, `wfpLift` (vocabulary)
and thirteen theorems; `A` is the conjunction of their types.  **Universes**: the project's
tangent functor lives on `EP.{max u 1}`, and `B` is stated on `EP.{1}` / `EPLoc.{1}` with
`EP.tangent.{0}`; so the item's theorems on `EP(E⁻¹)` are instantiated at `u = 0` (objects in
`EP.{max 0 1} = EP.{1}`), and the helper lemmas on unbundled ep-groupoids (`tangent_comp`,
`tangent_id`, `projLeft_comp_wfpLift`, `projRight_comp_wfpLift`) at universe `1`, the level at which
the project's proof uses them for `EP.{1}`.  The conjuncts: `theorem_11_1_1` (`T(X) = TX`,
`T[d] = [Td]`, refinements and equivalent diagrams go to refinements and equivalent diagrams,
`T` preserves `𝟙` and `≫`, `T ∘ i = i ∘ T`), `tangentFunctor_obj`, `tangentFunctor_map_homMk`,
`tangentFunctor_map_localizationFunctor`, `isGeneralizedIso_tangent`, `Diagram.IsRefinement.tangent`,
`Diagram.Equiv.tangent`, `isRefinement_tangent_id`, `isRefinement_tangent_comp` (`T(d ∘ e)` refines
`Td ∘ Te`), `projLeft_comp_wfpLift`, `projRight_comp_wfpLift`, `EpFunctor.tangent_comp`,
`EpFunctor.tangent_id`.

* `A_to_B`: `T := EPLoc.tangentFunctor`, `hobj := rfl` (so the `eqToHom`s are identities); the
  morphism formula and the commuting square (`Functor.ext`) from `theorem_11_1_1`.
* `B_to_A`: `B`'s functor `T` equals `tangentFunctor` (`Functor.ext`, from `hobj` and the
  morphism formula, every morphism being some `[d]`).  From `B` (through `T`, transported along
  `T = tangentFunctor` by `subst`): `T` preserves `𝟙` and `≫`; equivalent diagrams have equivalent
  tangents (`T[d] = T[d']`, cancel the `eqToHom`s); `T ∘ i = i ∘ T`; generalized isomorphisms go to
  generalized isomorphisms.  Not from `B`: the **refinement** statements (`IsRefinement.tangent`,
  `isRefinement_tangent_id`, `isRefinement_tangent_comp`; `B` only knows classes, and `Equiv` does
  not give a refinement in a prescribed direction) and the helper lemmas on unbundled ep-groupoids;
  these are re-proved outright (the project's proofs, copied, from non-item lemmas:
  `MPolyfold.tangentMap_comp`, `theorem_10_1_7`, `isEquivalence_projLeft`, `wfpLift`, ...).

**Harness note.**  `A`'s statement mentions `EPLoc.tangentFunctor`, whose fields `map_id`,
`map_comp`, and the well-definedness of `map` are proved with the banned `isRefinement_tangent_id`,
`isRefinement_tangent_comp`, `Diagram.Equiv.tangent` (abstracted as `tangentFunctor._proof_1..3`).
Every term mentioning `A` reaches them, so plain `#rt_check` fails (recorded with `#guard_msgs`);
`#rt_check_soft` passes: the proofs never use these fields (`B_to_A` uses the fields of `B`'s `T`). -/

namespace RoundTrip.V11_1
open Polyfold CategoryTheory
open Polyfold.EPLocalization Polyfold.WeakFibredProduct

/-- The project's statement (`u = 0` for `EP(E⁻¹)`, universe `1` for the unbundled helpers). -/
def A : Prop :=
  (type_of% @Polyfold.EPLocalization.EPLoc.theorem_11_1_1.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.tangentFunctor_obj.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.tangentFunctor_map_homMk.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.tangentFunctor_map_localizationFunctor.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.isGeneralizedIso_tangent.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.IsRefinement.tangent.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.Equiv.tangent.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.isRefinement_tangent_id.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.isRefinement_tangent_comp.{0}) ∧
  (type_of% @Polyfold.EPLocalization.projLeft_comp_wfpLift.{1}) ∧
  (type_of% @Polyfold.EPLocalization.projRight_comp_wfpLift.{1}) ∧
  (type_of% @Polyfold.EpFunctor.tangent_comp.{1, 1}) ∧
  (type_of% @Polyfold.EpFunctor.tangent_id.{1})

theorem A_holds : A :=
  ⟨@Polyfold.EPLocalization.EPLoc.theorem_11_1_1.{0},
    @Polyfold.EPLocalization.EPLoc.tangentFunctor_obj.{0},
    @Polyfold.EPLocalization.EPLoc.tangentFunctor_map_homMk.{0},
    @Polyfold.EPLocalization.EPLoc.tangentFunctor_map_localizationFunctor.{0},
    @Polyfold.EPLocalization.EPLoc.isGeneralizedIso_tangent.{0},
    @Polyfold.EPLocalization.Diagram.IsRefinement.tangent.{0},
    @Polyfold.EPLocalization.Diagram.Equiv.tangent.{0},
    @Polyfold.EPLocalization.Diagram.isRefinement_tangent_id.{0},
    @Polyfold.EPLocalization.Diagram.isRefinement_tangent_comp.{0},
    @Polyfold.EPLocalization.projLeft_comp_wfpLift.{1},
    @Polyfold.EPLocalization.projRight_comp_wfpLift.{1},
    @Polyfold.EpFunctor.tangent_comp.{1, 1}, @Polyfold.EpFunctor.tangent_id.{1}⟩

/-- `eqToHom`s of self-equalities are identities. -/
theorem eqToHom_conj {C : Type*} [Category C] {X Y : C} (p : X = X) (q : Y = Y) (g : X ⟶ Y) :
    eqToHom p ≫ g ≫ eqToHom q = g := by
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

theorem A_to_B : A → B := by
  rintro ⟨⟨-, hmap, -, -, -, -, hloc⟩, -⟩
  refine ⟨EPLoc.tangentFunctor.{0}, fun X => rfl, fun X Y d => (hmap d).trans
    (eqToHom_conj _ _ _).symm, CategoryTheory.Functor.ext (fun X => rfl) fun X Y Φ =>
      (hloc Φ).trans (eqToHom_conj _ _ _).symm⟩

/-! ### The refinement statements and the helpers, re-proved outright (the project's proofs) -/

section Copies

universe u v

section Tangent
variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {Obj'' Mor'' : Type u} [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
  [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor'']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {Z : EpGroupoid Obj'' Mor''}

theorem tangent_comp' (G : EpFunctor Y Z) (F : EpFunctor X Y) :
    (G.comp F).tangent = G.tangent.comp F.tangent :=
  EpFunctor.ext (MPolyfold.tangentMap_comp G.isScSmoothMap_obj F.isScSmoothMap_obj)
    (MPolyfold.tangentMap_comp G.isScSmoothMap_mor F.isScSmoothMap_mor)

theorem tangent_id' : (EpFunctor.id X).tangent = EpFunctor.id X.tangentEpGroupoid :=
  EpFunctor.ext MPolyfold.tangentMap_id MPolyfold.tangentMap_id

end Tangent

section Lift
variable {ObjX MorX : Type u} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {ObjY MorY : Type u} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjZ MorZ : Type u} [TopologicalSpace ObjZ] [T2Space ObjZ] [ParacompactSpace ObjZ]
  [TopologicalSpace MorZ] [T2Space MorZ] [ParacompactSpace MorZ]
  {ObjC MorC : Type u} [TopologicalSpace ObjC] [T2Space ObjC] [ParacompactSpace ObjC]
  [TopologicalSpace MorC] [T2Space MorC] [ParacompactSpace MorC]
  {X : EpGroupoid ObjX MorX} {Y : EpGroupoid ObjY MorY} {Z : EpGroupoid ObjZ MorZ}
  {C : EpGroupoid ObjC MorC} {Φ : EpFunctor X Y} {G : EpFunctor Z Y}
  (P : EpFunctor C X) (Q : EpFunctor C Z) (τ : EpNatTrans (Φ.comp P) (G.comp Q))

theorem projLeft_comp_wfpLift' (h : Admissible Φ G) :
    (projLeft Φ G h).comp (wfpLift P Q τ h) = P :=
  EpFunctor.ext rfl rfl

theorem projRight_comp_wfpLift' (h : Admissible Φ G) :
    (projRight Φ G h).comp (wfpLift P Q τ h) = Q :=
  EpFunctor.ext rfl rfl

end Lift

variable {X Y Z : EP.{max u 1}}

theorem isRefinement_tangent' {d d' : Diagram X Y} (h : d'.IsRefinement d) :
    d'.tangent.IsRefinement d.tangent := by
  obtain ⟨H, hH, ⟨σ⟩, ⟨τ⟩⟩ := h
  refine ⟨H.tangent, EpFunctor.theorem_10_1_7 hH, ⟨σ.tangent.castEq ?_ rfl⟩,
    ⟨τ.tangent.castEq ?_ rfl⟩⟩
  · exact tangent_comp' _ _
  · exact tangent_comp' _ _

theorem isRefinement_tangent_id' (X : EP.{max u 1}) :
    (Diagram.id X).tangent.IsRefinement (Diagram.id X.tangent) := by
  refine ⟨EpFunctor.id _, EpFunctor.IsEquivalence.id _, .of_eq ?_, .of_eq ?_⟩ <;>
  · change EpFunctor.id _ = (EpFunctor.id X.X).tangent
    rw [tangent_id']

theorem isRefinement_tangent_comp' (d : Diagram X Y) (e : Diagram Y Z) :
    (d.comp e).tangent.IsRefinement (d.tangent.comp e.tangent) := by
  have h := d.admissible e
  have h' : Admissible d.Φ.tangent e.F.tangent :=
    .of_isEquivalence_right (EpFunctor.theorem_10_1_7 e.isEquivalence_F)
  let πA := projLeft d.Φ e.F (d.admissible e)
  let πB := projRight d.Φ e.F (d.admissible e)
  let τ : EpNatTrans (d.Φ.tangent.comp πA.tangent) (e.F.tangent.comp πB.tangent) :=
    (natTrans d.Φ e.F (d.admissible e)).tangent.castEq (tangent_comp' _ _) (tangent_comp' _ _)
  let L := wfpLift πA.tangent πB.tangent τ h'
  have hL : L.IsEquivalence :=
    EpFunctor.IsEquivalence.of_comp_left
      (isEquivalence_projLeft (EpFunctor.theorem_10_1_7 e.isEquivalence_F) h')
      (by
        rw [projLeft_comp_wfpLift']
        exact EpFunctor.theorem_10_1_7 (isEquivalence_projLeft e.isEquivalence_F h))
  refine ⟨L, hL, .of_eq ?_, .of_eq ?_⟩
  · exact EpFunctor.ext
      (MPolyfold.tangentMap_comp d.F.isScSmoothMap_obj πA.isScSmoothMap_obj).symm
      (MPolyfold.tangentMap_comp d.F.isScSmoothMap_mor πA.isScSmoothMap_mor).symm
  · exact EpFunctor.ext
      (MPolyfold.tangentMap_comp e.Φ.isScSmoothMap_obj πB.isScSmoothMap_obj).symm
      (MPolyfold.tangentMap_comp e.Φ.isScSmoothMap_mor πB.isScSmoothMap_mor).symm

end Copies

/-! ### `B ⇒ A` -/

theorem B_to_A : B → A := by
  · intro hB
    obtain ⟨T, hobj, hmap, hcompat⟩ := hB
    -- facts about `B`'s functor `T`
    have hid : ∀ X : EPLoc.{1}, T.map (𝟙 X) = 𝟙 (T.obj X) := T.map_id
    have hcomp : ∀ {X Y Z : EPLoc.{1}} (f : X ⟶ Y) (g : Y ⟶ Z), T.map (f ≫ g) = T.map f ≫ T.map g :=
      fun f g => T.map_comp f g
    have hequiv : ∀ {X Y : EP.{1}} {d d' : Diagram X Y}, Diagram.Equiv d d' →
        Diagram.Equiv (Diagram.tangent.{0} d) (Diagram.tangent.{0} d') := by
      intro X Y d d' h
      have e : T.map (EPLoc.homMk d) = T.map (EPLoc.homMk d') :=
        congrArg T.map (EPLoc.homMk_eq_homMk_iff.2 h)
      rw [hmap, hmap] at e
      exact EPLoc.homMk_eq_homMk_iff.1 ((cancel_mono _).1 ((cancel_epi _).1 e))
    have hiso : ∀ {X Y : EPLoc.{1}} {f : X ⟶ Y}, EPLoc.IsGeneralizedIso f →
        EPLoc.IsGeneralizedIso (T.map f) := by
      rintro X Y f ⟨g, h₁, h₂⟩
      exact ⟨T.map g, by rw [← hcomp, h₁, hid], by rw [← hcomp, h₂, hid]⟩
    have hloc : ∀ {X Y : EP.{1}} (Φ : X ⟶ Y), T.map (EPLoc.localizationFunctor.map Φ) =
        eqToHom (Functor.congr_obj hcompat X) ≫
          EPLoc.localizationFunctor.map (Polyfold.tangentFunctor.{0}.map Φ) ≫
            eqToHom (Functor.congr_obj hcompat Y).symm :=
      fun Φ => Functor.congr_hom hcompat Φ
    -- `T` is the project's `tangentFunctor`
    have hT : T = EPLoc.tangentFunctor.{0} := by
      refine CategoryTheory.Functor.ext hobj fun X Y f => ?_
      obtain ⟨d, rfl⟩ := EPLoc.homMk_surjective (X := X.toEP) (Y := Y.toEP) f
      exact hmap X.toEP Y.toEP d
    subst hT
    have hloc' : ∀ {X Y : EP.{1}} (Φ : X ⟶ Y),
        EPLoc.tangentFunctor.{0}.map (EPLoc.localizationFunctor.map Φ) =
          EPLoc.localizationFunctor.map (Polyfold.tangentFunctor.{0}.map Φ) := by
      intro X Y Φ
      exact (hloc Φ).trans (eqToHom_conj _ _ _)
    exact ⟨⟨fun _ => rfl, fun _ => rfl, fun h => isRefinement_tangent'.{0} h, hequiv, hid, hcomp,
        hloc'⟩, fun _ => rfl, fun _ => rfl, hloc', hiso, fun h => isRefinement_tangent'.{0} h,
      hequiv, isRefinement_tangent_id'.{0}, isRefinement_tangent_comp'.{0},
      projLeft_comp_wfpLift'.{1}, projRight_comp_wfpLift'.{1}, tangent_comp'.{1, 1},
      tangent_id'.{1}⟩

/--
error: rt_check FAIL: RoundTrip.V11_1.A_to_B uses [Polyfold.EPLocalization.Diagram.IsRefinement.tangent,
 Polyfold.EPLocalization.Diagram.Equiv.tangent,
 Polyfold.EPLocalization.Diagram.isRefinement_tangent_id,
 Polyfold.EPLocalization.Diagram.isRefinement_tangent_comp,
 Polyfold.EPLocalization.projLeft_comp_wfpLift,
 Polyfold.EpFunctor.tangent_comp,
 Polyfold.EpFunctor.tangent_id]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V11_1.A_to_B [Polyfold.EPLocalization.EPLoc.theorem_11_1_1,
  Polyfold.EPLocalization.EPLoc.tangentFunctor_obj,
  Polyfold.EPLocalization.EPLoc.tangentFunctor_map_homMk,
  Polyfold.EPLocalization.EPLoc.tangentFunctor_map_localizationFunctor,
  Polyfold.EPLocalization.EPLoc.isGeneralizedIso_tangent,
  Polyfold.EPLocalization.Diagram.IsRefinement.tangent,
  Polyfold.EPLocalization.Diagram.Equiv.tangent,
  Polyfold.EPLocalization.Diagram.isRefinement_tangent_id,
  Polyfold.EPLocalization.Diagram.isRefinement_tangent_comp,
  Polyfold.EPLocalization.projLeft_comp_wfpLift, Polyfold.EPLocalization.projRight_comp_wfpLift,
  Polyfold.EpFunctor.tangent_comp, Polyfold.EpFunctor.tangent_id]
/--
error: rt_check FAIL: RoundTrip.V11_1.B_to_A uses [Polyfold.EPLocalization.Diagram.IsRefinement.tangent,
 Polyfold.EPLocalization.Diagram.Equiv.tangent,
 Polyfold.EPLocalization.Diagram.isRefinement_tangent_id,
 Polyfold.EPLocalization.Diagram.isRefinement_tangent_comp,
 Polyfold.EPLocalization.projLeft_comp_wfpLift,
 Polyfold.EpFunctor.tangent_comp,
 Polyfold.EpFunctor.tangent_id]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V11_1.B_to_A [Polyfold.EPLocalization.EPLoc.theorem_11_1_1,
  Polyfold.EPLocalization.EPLoc.tangentFunctor_obj,
  Polyfold.EPLocalization.EPLoc.tangentFunctor_map_homMk,
  Polyfold.EPLocalization.EPLoc.tangentFunctor_map_localizationFunctor,
  Polyfold.EPLocalization.EPLoc.isGeneralizedIso_tangent,
  Polyfold.EPLocalization.Diagram.IsRefinement.tangent,
  Polyfold.EPLocalization.Diagram.Equiv.tangent,
  Polyfold.EPLocalization.Diagram.isRefinement_tangent_id,
  Polyfold.EPLocalization.Diagram.isRefinement_tangent_comp,
  Polyfold.EPLocalization.projLeft_comp_wfpLift, Polyfold.EPLocalization.projRight_comp_wfpLift,
  Polyfold.EpFunctor.tangent_comp, Polyfold.EpFunctor.tangent_id]

#rt_check_soft RoundTrip.V11_1.A_to_B [Polyfold.EPLocalization.EPLoc.theorem_11_1_1,
  Polyfold.EPLocalization.EPLoc.tangentFunctor_obj,
  Polyfold.EPLocalization.EPLoc.tangentFunctor_map_homMk,
  Polyfold.EPLocalization.EPLoc.tangentFunctor_map_localizationFunctor,
  Polyfold.EPLocalization.EPLoc.isGeneralizedIso_tangent,
  Polyfold.EPLocalization.Diagram.IsRefinement.tangent,
  Polyfold.EPLocalization.Diagram.Equiv.tangent,
  Polyfold.EPLocalization.Diagram.isRefinement_tangent_id,
  Polyfold.EPLocalization.Diagram.isRefinement_tangent_comp,
  Polyfold.EPLocalization.projLeft_comp_wfpLift, Polyfold.EPLocalization.projRight_comp_wfpLift,
  Polyfold.EpFunctor.tangent_comp, Polyfold.EpFunctor.tangent_id]
#rt_check_soft RoundTrip.V11_1.B_to_A [Polyfold.EPLocalization.EPLoc.theorem_11_1_1,
  Polyfold.EPLocalization.EPLoc.tangentFunctor_obj,
  Polyfold.EPLocalization.EPLoc.tangentFunctor_map_homMk,
  Polyfold.EPLocalization.EPLoc.tangentFunctor_map_localizationFunctor,
  Polyfold.EPLocalization.EPLoc.isGeneralizedIso_tangent,
  Polyfold.EPLocalization.Diagram.IsRefinement.tangent,
  Polyfold.EPLocalization.Diagram.Equiv.tangent,
  Polyfold.EPLocalization.Diagram.isRefinement_tangent_id,
  Polyfold.EPLocalization.Diagram.isRefinement_tangent_comp,
  Polyfold.EPLocalization.projLeft_comp_wfpLift, Polyfold.EPLocalization.projRight_comp_wfpLift,
  Polyfold.EpFunctor.tangent_comp, Polyfold.EpFunctor.tangent_id]
#rt_overlap RoundTrip.V11_1.B_to_A [Polyfold.EPLocalization.EPLoc.theorem_11_1_1,
  Polyfold.EPLocalization.EPLoc.tangentFunctor_obj,
  Polyfold.EPLocalization.EPLoc.tangentFunctor_map_homMk,
  Polyfold.EPLocalization.EPLoc.tangentFunctor_map_localizationFunctor,
  Polyfold.EPLocalization.EPLoc.isGeneralizedIso_tangent,
  Polyfold.EPLocalization.Diagram.IsRefinement.tangent,
  Polyfold.EPLocalization.Diagram.Equiv.tangent,
  Polyfold.EPLocalization.Diagram.isRefinement_tangent_id,
  Polyfold.EPLocalization.Diagram.isRefinement_tangent_comp,
  Polyfold.EPLocalization.projLeft_comp_wfpLift, Polyfold.EPLocalization.projRight_comp_wfpLift,
  Polyfold.EpFunctor.tangent_comp, Polyfold.EpFunctor.tangent_id]

end RoundTrip.V11_1
