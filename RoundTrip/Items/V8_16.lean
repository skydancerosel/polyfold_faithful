import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_16

/-! Round trip for V8_16 (after Definition 8.1.13 = 2017 Definition 8.1, 2017 p. 267: natural
equivalence is an equivalence relation).

The item lists the definitions `EpNatTrans.refl`, `.symm`, `.trans`, `.whiskerLeft`,
`.whiskerRight` (vocabulary) and seven theorems.  `A` is the conjunction of the types of the
theorems, universes at `0` (B lives in `Type`): `EpNatTrans.isScSmoothMap_comp_app` (the
composite `x ↦ τ'(x) ∘ τ(x)` is sc-smooth), `EpFunctor.NaturallyEquivalent.refl`, `.symm`,
`.trans`, `EpFunctor.naturallyEquivalent_equivalence` (the text's claim), and the whiskering
results `NaturallyEquivalent.comp_left`, `.comp_right` (not in the text).

`B`: for all ep-groupoids `X`, `Y` in `Type`, B's own reading `NatEquivB` of `F ≃ G` is an
equivalence relation on `EpFunctor X Y`.

* `NatEquivB F G ↔ F.NaturallyEquivalent G` (`natEquivB_iff`): the fields of `EpNatTrans` are
  B's conditions (as in V8_15).
* `A ⇒ B`: transport `naturallyEquivalent_equivalence` along that iff.
* `B ⇒ A`: `refl`, `symm`, `trans` and the equivalence come from `B` along the iff.  The other
  three conjuncts are not consequences of `B` (B's transitivity gives *some* natural
  transformation `F → H`, not the sc-smoothness of the particular composite; whiskering is
  about functors between three ep-groupoids) and are re-proved outright here: the sc-smoothness
  of `x ↦ τ'(x) ∘ τ(x)` by the sheet form of Definition 7.3 (4)
  (`EpGroupoid.isScSmoothCompSheet`, not in the item) and local sc-smoothness, and the whiskered
  transformations `x ↦ τ(E x)`, `x ↦ K(τ x)` (constructed here, not with the item's
  `whiskerLeft`/`whiskerRight`).
-/

namespace RoundTrip.V8_16
open Polyfold Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpNatTrans.isScSmoothMap_comp_app.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.NaturallyEquivalent.refl.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.NaturallyEquivalent.symm.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.NaturallyEquivalent.trans.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.naturallyEquivalent_equivalence.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.NaturallyEquivalent.comp_left.{0, 0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.NaturallyEquivalent.comp_right.{0, 0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.EpNatTrans.isScSmoothMap_comp_app.{0, 0},
    @Polyfold.EpFunctor.NaturallyEquivalent.refl.{0, 0},
    @Polyfold.EpFunctor.NaturallyEquivalent.symm.{0, 0},
    @Polyfold.EpFunctor.NaturallyEquivalent.trans.{0, 0},
    @Polyfold.EpFunctor.naturallyEquivalent_equivalence.{0, 0},
    @Polyfold.EpFunctor.NaturallyEquivalent.comp_left.{0, 0, 0},
    @Polyfold.EpFunctor.NaturallyEquivalent.comp_right.{0, 0, 0}⟩

section Glue
variable {Obj Mor Obj' Mor' : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

/-- The project natural transformation with `app = τ`, built from B's conditions. -/
def ofB {F G : EpFunctor X Y} (τ : Obj → Mor') (hτ : IsNatTransB F G τ) : EpNatTrans F G where
  app := τ
  isScSmoothMap_app := hτ.1
  src_app x := (hτ.2.1 x).1
  tgt_app x := (hτ.2.1 x).2
  naturality h := hτ.2.2 h _ _ rfl rfl

theorem natEquivB_iff (F G : EpFunctor X Y) : NatEquivB F G ↔ F.NaturallyEquivalent G := by
  constructor
  · rintro ⟨τ, hτ⟩
    exact ⟨ofB τ hτ⟩
  · rintro ⟨τ⟩
    refine ⟨τ.app, τ.isScSmoothMap_app, fun x => ⟨τ.src_app x, τ.tgt_app x⟩, ?_⟩
    rintro h x x' rfl rfl
    exact τ.naturality h

end Glue

theorem A_to_B : A → B := by
  intro hA Obj Mor Obj' Mor' _ _ _ _ _ _ _ _ _ _ _ _ X Y
  have hE := hA.2.2.2.2.1 (X := X) (Y := Y)
  refine ⟨fun F => (natEquivB_iff F F).2 (hE.refl F), fun {F G} h =>
    (natEquivB_iff G F).2 (hE.symm ((natEquivB_iff F G).1 h)), fun {F G H} h h' =>
    (natEquivB_iff F H).2 (hE.trans ((natEquivB_iff F G).1 h) ((natEquivB_iff G H).1 h'))⟩

/-! ### `B ⇒ A` -/

section Outright
variable {Obj Mor Obj' Mor' Obj'' Mor'' : Type}
  [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
  [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor'']

/-- The composite `x ↦ τ'(x) ∘ τ(x)` is sc-smooth (re-proved: sheet form of Definition 7.3 (4)). -/
theorem compApp_smooth {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}
    {F G H : EpFunctor X Y} (τ : EpNatTrans F G) (τ' : EpNatTrans G H) :
    X.PObj.IsScSmoothMap Y.PMor fun x => Y.comp (τ'.app x) (τ.app x) := by
  have hc' : Continuous τ'.app := continuousOn_univ.1 τ'.isScSmoothMap_app.continuousOn
  refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun x₀ _ => ?_
  obtain ⟨W, V, σ, hW, hd⟩ := Y.isLocalScDiffeo_src (τ'.app x₀)
  have hU : IsOpen (τ'.app ⁻¹' W) := hd.isScSmoothOn.isOpen.preimage hc'
  have hmaps : MapsTo τ.app (τ'.app ⁻¹' W) (Y.tgt ⁻¹' V) := fun x hx => by
    change Y.tgt (τ.app x) ∈ V
    rw [τ.tgt_app, ← τ'.src_app]
    exact hd.mapsTo hx
  refine ⟨τ'.app ⁻¹' W, hU, hW, subset_univ _, ?_⟩
  refine (MPolyfold.IsScSmoothOn.comp (Y.isScSmoothCompSheet σ W V hd)
    (τ.isScSmoothMap_app.mono hU (subset_univ _)) hmaps).congr fun x hx => ?_
  simp only [Function.comp_apply]
  rw [τ.tgt_app, ← τ'.src_app, hd.left_inv _ hx]

theorem compLeft {W : EpGroupoid Obj Mor} {X : EpGroupoid Obj' Mor'}
    {Y : EpGroupoid Obj'' Mor''} (E : EpFunctor W X) {F G : EpFunctor X Y}
    (h : F.NaturallyEquivalent G) : (F.comp E).NaturallyEquivalent (G.comp E) := by
  obtain ⟨τ⟩ := h
  refine ⟨⟨fun w => τ.app (E.obj w), τ.isScSmoothMap_app.comp E.isScSmoothMap_obj,
    fun w => τ.src_app (E.obj w), fun w => τ.tgt_app (E.obj w), fun h => ?_⟩⟩
  have hn := τ.naturality (E.mor h)
  rw [E.tgt_mor, E.src_mor] at hn
  exact hn

theorem compRight {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}
    {Z : EpGroupoid Obj'' Mor''} {F G : EpFunctor X Y} (h : F.NaturallyEquivalent G)
    (K : EpFunctor Y Z) : (K.comp F).NaturallyEquivalent (K.comp G) := by
  obtain ⟨τ⟩ := h
  refine ⟨⟨fun x => K.mor (τ.app x), K.isScSmoothMap_mor.comp τ.isScSmoothMap_app,
    fun x => ?_, fun x => ?_, fun h => ?_⟩⟩
  · change Z.src (K.mor (τ.app x)) = K.obj (F.obj x)
    rw [K.src_mor, τ.src_app]
  · change Z.tgt (K.mor (τ.app x)) = K.obj (G.obj x)
    rw [K.tgt_mor, τ.tgt_app]
  · change Z.comp (K.mor (τ.app (X.tgt h))) (K.mor (F.mor h)) =
      Z.comp (K.mor (G.mor h)) (K.mor (τ.app (X.src h)))
    rw [← K.mor_comp _ _ (by rw [τ.src_app, F.tgt_mor]), τ.naturality h,
      K.mor_comp _ _ (by rw [G.src_mor, τ.tgt_app])]

end Outright

theorem B_to_A : B → A := by
  intro hB
  -- the relation of `B`, transported to the project's `NaturallyEquivalent`
  have hE : ∀ (Obj Mor Obj' Mor' : Type) [TopologicalSpace Obj] [T2Space Obj]
      [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
      [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
      [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
      (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor'),
      Equivalence (EpFunctor.NaturallyEquivalent (X := X) (Y := Y)) := by
    intro Obj Mor Obj' Mor' _ _ _ _ _ _ _ _ _ _ _ _ X Y
    have hb := hB Obj Mor Obj' Mor' X Y
    exact ⟨fun F => (natEquivB_iff F F).1 (hb.refl F), fun {F G} h =>
      (natEquivB_iff G F).1 (hb.symm ((natEquivB_iff F G).2 h)), fun {F G H} h h' =>
      (natEquivB_iff F H).1 (hb.trans ((natEquivB_iff F G).2 h) ((natEquivB_iff G H).2 h'))⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F G H τ τ'
    exact compApp_smooth τ τ'
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F
    exact (hE Obj Mor Obj' Mor' X Y).refl F
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F G h
    exact (hE Obj Mor Obj' Mor' X Y).symm h
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F G H h h'
    exact (hE Obj Mor Obj' Mor' X Y).trans h h'
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y
    exact hE Obj Mor Obj' Mor' X Y
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ Obj'' Mor'' _ _ _ _ _ _ W X Y E F G h
    exact compLeft E h
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ Obj'' Mor'' _ _ _ _ _ _ X Y Z F G h K
    exact compRight h K

#rt_check RoundTrip.V8_16.A_to_B [Polyfold.EpNatTrans.isScSmoothMap_comp_app,
  Polyfold.EpFunctor.NaturallyEquivalent.refl, Polyfold.EpFunctor.NaturallyEquivalent.symm,
  Polyfold.EpFunctor.NaturallyEquivalent.trans,
  Polyfold.EpFunctor.naturallyEquivalent_equivalence,
  Polyfold.EpFunctor.NaturallyEquivalent.comp_left,
  Polyfold.EpFunctor.NaturallyEquivalent.comp_right]
#rt_check RoundTrip.V8_16.B_to_A [Polyfold.EpNatTrans.isScSmoothMap_comp_app,
  Polyfold.EpFunctor.NaturallyEquivalent.refl, Polyfold.EpFunctor.NaturallyEquivalent.symm,
  Polyfold.EpFunctor.NaturallyEquivalent.trans,
  Polyfold.EpFunctor.naturallyEquivalent_equivalence,
  Polyfold.EpFunctor.NaturallyEquivalent.comp_left,
  Polyfold.EpFunctor.NaturallyEquivalent.comp_right]
#rt_overlap RoundTrip.V8_16.B_to_A [Polyfold.EpNatTrans.isScSmoothMap_comp_app,
  Polyfold.EpFunctor.NaturallyEquivalent.refl, Polyfold.EpFunctor.NaturallyEquivalent.symm,
  Polyfold.EpFunctor.NaturallyEquivalent.trans,
  Polyfold.EpFunctor.naturallyEquivalent_equivalence,
  Polyfold.EpFunctor.NaturallyEquivalent.comp_left,
  Polyfold.EpFunctor.NaturallyEquivalent.comp_right]

end RoundTrip.V8_16
