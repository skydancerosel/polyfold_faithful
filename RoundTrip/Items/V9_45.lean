import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_45

/-! Round trip for V9_45 (Definition 9.4.7, 2021 p. 432; 2017: Definition 9.14): `y`-equivalence
of sheets, `T_yMᵢ = T_yMᵢ'` for `i ∼_y i'`, `P_y = I_y / ∼_y`.

`A` is the conjunction of the types of the two listed theorems, universes instantiated at `0`
(`B` lives in `Type`): `MPolyfold.SheetGeometry.equivalence_yEquiv` and
`MPolyfold.SheetGeometry.submanifoldTangent_eq_of_yEquiv`.  `IsLink`, `YEquiv`, `ySetoid` and
`numClasses` are definitions (vocabulary).

Neither direction is proved; the difference is genuine.

* The definitions have the same shape: `YEquiv` is the reflexive-transitive closure of the links
  `y ∈ K(i, j)^e` (reference sheet `Mᵢ`) on `I_y`, as `B`'s `YEquivB`, and the project's
  `numClasses` (the quotient by the equivalence closure `ySetoid`) is the number of classes of
  `Quot (YEquiv)`, `B`'s formula (`numClasses_eq_card_quot`, any `SheetGeometry`).
* `A → B` fails.  `A` is stated for an abstract `SheetGeometry` `G` on an M-polyfold `P`, with
  Lemma 9.4.4 (`ess_comm`) and the note `T_zN = T_zN'` at essential points
  (`submanifoldTangent_eq`) as *fields*; `equivalence_yEquiv` and
  `submanifoldTangent_eq_of_yEquiv` are their bookkeeping consequences (symmetry of the links,
  induction along the chain).  `B` asks for exactly these two facts, unconditionally, for sheets
  that are immersed `n`-manifolds with corners `jᵢ : Nᵢ → F` in a Banach space.  To get
  `B`'s equivalence from `equivalence_yEquiv` one needs a `G` whose links at the points of `F`
  are `B`'s links; its field `ess_comm` is then Lemma 9.4.4 for `B`'s sheets (essential points
  of `Mᵢ ∩ Mᵢ'` for `Nᵢ` and for `Nᵢ'` agree), which is not in the project for Mathlib manifolds
  immersed in `F` (a `G` whose links are `B`'s links or their reverses can be built on a
  discrete M-polyfold, see V9_46, but it only gives the equivalence closure).  `B`'s tangent claim
  is about `T_yMᵢ = Djᵢ(ℝⁿ) ⊆ F`, which `A`'s `P.submanifoldTangent` (Part I's tangent bundle of
  an M-polyfold) does not express: there is no M-polyfold structure on `F` (an arbitrary Banach
  space) identifying the two, and the note itself (`T_{zₖ}Mᵢ = T_{zₖ}Mᵢ'` at full points, then the
  limit) would have to be proved in `B`'s model.
* `B → A` fails.  `A` holds for every `SheetGeometry` (any M-polyfold, any data satisfying the
  fields), `B` only for its concrete model; `B` says nothing about abstract data.  (`A` has a
  short direct proof from the fields, which would not use `B`.)
-/

namespace RoundTrip.V9_45
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.MPolyfold.SheetGeometry.equivalence_yEquiv.{0, 0}) ∧
  (type_of% @Polyfold.MPolyfold.SheetGeometry.submanifoldTangent_eq_of_yEquiv.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.SheetGeometry.equivalence_yEquiv.{0, 0},
    @Polyfold.MPolyfold.SheetGeometry.submanifoldTangent_eq_of_yEquiv.{0, 0}⟩

/-- **The definitions agree on `♯P_y`**: the project's `numClasses` (quotient by the equivalence
closure `ySetoid` of the links) is the number of classes of `Quot (YEquiv)`, the chain relation,
which is `B`'s formula `Nat.card (Quot (YEquivB y))`.  No `SheetGeometry` field is used. -/
theorem numClasses_eq_card_quot {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    {P : MPolyfold X} {S : Set (Set X)} (G : P.SheetGeometry S) {ι : Type} (M : ι → Set X)
    (y : X) : G.numClasses M y = Nat.card (Quot (G.YEquiv M y)) := by
  have hle : ∀ {a b}, G.YEquiv M y a b → Relation.EqvGen (G.IsLink M y) a b := by
    intro a b h
    induction h with
    | refl => exact Relation.EqvGen.refl _
    | tail _ hbc ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ hbc)
  let f : Quotient (G.ySetoid M y) → Quot (G.YEquiv M y) :=
    Quotient.lift (Quot.mk _) fun a b hab => by
      refine Quot.eqvGen_sound ?_
      change Relation.EqvGen _ a b at hab
      exact hab.mono fun a b h => Relation.ReflTransGen.single h
  let g : Quot (G.YEquiv M y) → Quotient (G.ySetoid M y) :=
    Quot.lift (Quotient.mk _) fun a b hab => Quotient.sound (hle hab)
  have e : Quotient (G.ySetoid M y) ≃ Quot (G.YEquiv M y) :=
    { toFun := f, invFun := g
      left_inv := fun q => Quotient.inductionOn q fun _ => rfl
      right_inv := fun q => Quot.inductionOn q fun _ => rfl }
  exact Nat.card_congr e

#rt_check RoundTrip.V9_45.numClasses_eq_card_quot
  [Polyfold.MPolyfold.SheetGeometry.equivalence_yEquiv,
  Polyfold.MPolyfold.SheetGeometry.submanifoldTangent_eq_of_yEquiv]

end RoundTrip.V9_45
