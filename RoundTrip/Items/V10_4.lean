import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_4

/-!
Round trip for V10_4 (2021 Definition 10.1.4, p. 463 (2017: Definition 10.2, p. 335): natural
transformations and natural equivalence; the claims after it, p. 464).

The item lists the definitions `EpNatTrans`, `EpFunctor.NaturallyEquivalent`,
`EpNatTrans.toNatIso` (vocabulary) and four theorems.  `A` is the conjunction of the types of the
theorems, universes at `0`: `definition_10_1_4` (`≃` is an equivalence relation, and
`F ≃ G ⇒ F ∘ Ψ ≃ G ∘ Ψ`, `Φ ∘ F ≃ Φ ∘ G`), `EpFunctor.naturallyEquivalent_equivalence`,
`NaturallyEquivalent.comp_left`, `NaturallyEquivalent.comp_right`.

`B` says the project's `EpNatTrans F G` are exactly the blind author's natural transformations
(`IsNatTransB`, with naturality stated for `φ : x → x'`), `NaturallyEquivalent` is `NatEqB`, `NatEqB`
is an equivalence relation, and `F ≃ F'`, `G ≃ G'` give `H ≃ H'` for any functors `H = G ∘ F`,
`H' = G' ∘ F'` on objects and morphisms.

* `A ⇒ B`: the vocabulary part is structural (the fields of `EpNatTrans`; naturality for `φ`
  with `s φ = x`, `t φ = x'` after `subst`), and does not need `A`.  The equivalence relation is
  `A`'s `naturallyEquivalent_equivalence` transported along the iff.  Compatibility:
  `H = G.comp F`, `H' = G'.comp F'` (`EpFunctor.ext`), and `G ∘ F ≃ G ∘ F'` (`A`'s `comp_right`),
  `G ∘ F' ≃ G' ∘ F'` (`A`'s `comp_left`), then transitivity.
* `B ⇒ A`: everything from `B`: the equivalence relation transported back along the iff;
  `comp_left` (resp. `comp_right`) is `B`'s compatibility with `Ψ ≃ Ψ` (resp. `Φ ≃ Φ`) from `B`'s
  reflexivity on the appropriate pair of ep-groupoids.
-/

namespace RoundTrip.V10_4
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.definition_10_1_4.{0, 0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.naturallyEquivalent_equivalence.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.NaturallyEquivalent.comp_left.{0, 0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.NaturallyEquivalent.comp_right.{0, 0, 0})

theorem A_holds : A :=
  ⟨@definition_10_1_4.{0, 0, 0}, @EpFunctor.naturallyEquivalent_equivalence.{0, 0},
    @EpFunctor.NaturallyEquivalent.comp_left.{0, 0, 0},
    @EpFunctor.NaturallyEquivalent.comp_right.{0, 0, 0}⟩

/-! ### The vocabulary: `EpNatTrans` is `IsNatTransB` -/

section Glue

variable {Obj Mor Obj' Mor' : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

theorem isNatTransB_app {F G : EpFunctor X Y} (τ : EpNatTrans F G) : IsNatTransB F G τ.app := by
  refine ⟨τ.isScSmoothMap_app, fun x => ⟨τ.src_app x, τ.tgt_app x⟩, ?_⟩
  rintro φ x x' rfl rfl
  exact τ.naturality φ

/-- A blind natural transformation, as an `EpNatTrans`. -/
def ofIsNatTransB {F G : EpFunctor X Y} {τ : Obj → Mor'} (h : IsNatTransB F G τ) :
    EpNatTrans F G where
  app := τ
  isScSmoothMap_app := h.1
  src_app x := (h.2.1 x).1
  tgt_app x := (h.2.1 x).2
  naturality φ := h.2.2 φ _ _ rfl rfl

theorem naturallyEquivalent_iff (F G : EpFunctor X Y) : F.NaturallyEquivalent G ↔ NatEqB F G :=
  ⟨fun ⟨τ⟩ => ⟨τ.app, isNatTransB_app τ⟩, fun ⟨_, h⟩ => ⟨ofIsNatTransB h⟩⟩

end Glue

/-! ### `A ⇒ B` -/

theorem A_to_B : A → B := by
  intro hA Obj Mor Obj' Mor' Obj'' Mor'' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X Y Z
  have hequiv : Equivalence (fun F G : EpFunctor X Y => NatEqB F G) := by
    have h := hA.2.1 (X := X) (Y := Y)
    refine ⟨fun F => (naturallyEquivalent_iff F F).1 (h.refl F), fun hFG => ?_,
      fun hFG hGH => ?_⟩
    · exact (naturallyEquivalent_iff _ _).1 (h.symm ((naturallyEquivalent_iff _ _).2 hFG))
    · exact (naturallyEquivalent_iff _ _).1 (h.trans ((naturallyEquivalent_iff _ _).2 hFG)
        ((naturallyEquivalent_iff _ _).2 hGH))
  refine ⟨fun F G => ⟨isNatTransB_app, fun τ h => ⟨ofIsNatTransB h, rfl⟩,
    naturallyEquivalent_iff F G⟩, hequiv, ?_⟩
  intro F F' G G' H H' hHo hHm hH'o hH'm hF hG
  have e1 : H = G.comp F := EpFunctor.ext hHo hHm
  have e2 : H' = G'.comp F' := EpFunctor.ext hH'o hH'm
  subst e1 e2
  have h1 : (G.comp F).NaturallyEquivalent (G.comp F') :=
    hA.2.2.2 ((naturallyEquivalent_iff _ _).2 hF) G
  have h2 : (G.comp F').NaturallyEquivalent (G'.comp F') :=
    hA.2.2.1 F' ((naturallyEquivalent_iff _ _).2 hG)
  exact (naturallyEquivalent_iff _ _).1 ((hA.2.1 (X := X) (Y := Z)).trans h1 h2)

/-! ### `B ⇒ A` -/

theorem B_to_A : B → A := by
  intro hB
  -- the equivalence relation, for any pair of ep-groupoids (`Z := Y` is a dummy choice)
  have hEq : ∀ {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
      {Obj' Mor' : Type} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
      [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
      {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'},
      Equivalence (EpFunctor.NaturallyEquivalent (X := X) (Y := Y)) := by
    intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y
    have h := (hB Obj Mor Obj' Mor' Obj' Mor' X Y Y).2.1
    refine ⟨fun F => (naturallyEquivalent_iff F F).2 (h.refl F), fun hFG => ?_,
      fun hFG hGH => ?_⟩
    · exact (naturallyEquivalent_iff _ _).2 (h.symm ((naturallyEquivalent_iff _ _).1 hFG))
    · exact (naturallyEquivalent_iff _ _).2 (h.trans ((naturallyEquivalent_iff _ _).1 hFG)
        ((naturallyEquivalent_iff _ _).1 hGH))
  -- `F ≃ G ⇒ F ∘ E ≃ G ∘ E`
  have hL : ∀ {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
      {Obj' Mor' : Type} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
      [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
      {Obj'' Mor'' : Type} [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
      [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor'']
      {W : EpGroupoid Obj Mor} {X : EpGroupoid Obj' Mor'} {Y : EpGroupoid Obj'' Mor''}
      (E : EpFunctor W X) {F G : EpFunctor X Y}, F.NaturallyEquivalent G →
      (F.comp E).NaturallyEquivalent (G.comp E) := by
    intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ Obj'' Mor'' _ _ _ _ _ _ W X Y E F G h
    exact (naturallyEquivalent_iff _ _).2 ((hB _ _ _ _ _ _ W X Y).2.2 E E F G (F.comp E)
      (G.comp E) rfl rfl rfl rfl ((naturallyEquivalent_iff E E).1 (hEq.refl E))
      ((naturallyEquivalent_iff _ _).1 h))
  -- `F ≃ G ⇒ K ∘ F ≃ K ∘ G`
  have hR : ∀ {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
      {Obj' Mor' : Type} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
      [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
      {Obj'' Mor'' : Type} [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
      [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor'']
      {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {Z : EpGroupoid Obj'' Mor''}
      {F G : EpFunctor X Y}, F.NaturallyEquivalent G → ∀ K : EpFunctor Y Z,
      (K.comp F).NaturallyEquivalent (K.comp G) := by
    intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ Obj'' Mor'' _ _ _ _ _ _ X Y Z F G h K
    exact (naturallyEquivalent_iff _ _).2 ((hB _ _ _ _ _ _ X Y Z).2.2 F G K K (K.comp F)
      (K.comp G) rfl rfl rfl rfl ((naturallyEquivalent_iff _ _).1 h)
      ((naturallyEquivalent_iff K K).1 (hEq.refl K)))
  exact ⟨fun {_ _} _ _ _ _ _ _ {_ _} _ _ _ _ _ _ {_ _} _ _ _ _ _ _ {_ _ _} =>
      ⟨hEq, fun h Ψ => hL Ψ h, fun h Φ => hR h Φ⟩,
    @hEq, @hL, @hR⟩

#rt_check RoundTrip.V10_4.A_to_B [Polyfold.definition_10_1_4,
  Polyfold.EpFunctor.naturallyEquivalent_equivalence,
  Polyfold.EpFunctor.NaturallyEquivalent.comp_left,
  Polyfold.EpFunctor.NaturallyEquivalent.comp_right]
#rt_check RoundTrip.V10_4.B_to_A [Polyfold.definition_10_1_4,
  Polyfold.EpFunctor.naturallyEquivalent_equivalence,
  Polyfold.EpFunctor.NaturallyEquivalent.comp_left,
  Polyfold.EpFunctor.NaturallyEquivalent.comp_right]
#rt_overlap RoundTrip.V10_4.B_to_A [Polyfold.definition_10_1_4,
  Polyfold.EpFunctor.naturallyEquivalent_equivalence,
  Polyfold.EpFunctor.NaturallyEquivalent.comp_left,
  Polyfold.EpFunctor.NaturallyEquivalent.comp_right]

end RoundTrip.V10_4
