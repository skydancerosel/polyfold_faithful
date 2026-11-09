import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_1

/-!
Round trip for V10_1 (2021 Definition 10.1.1, p. 461 (2017: Definition 10.1, p. 333):
equivalences of ep-groupoids and the class `E`).

The item lists the definitions `EpFunctor.IsEquivalence`, `EP.equivalences` and
`Examples.pairToPoint` (vocabulary) and nine theorems.  `A` is the conjunction of the types of
the theorems, universes at `0`: `GroupoidFunctor.full_iff`, `faithful_iff`, `essSurj_iff` (full,
faithful, essentially surjective in terms of the structure maps, for arbitrary groupoids),
`IsEquivalence.essSurj`, `exists_iso`, `exists_mor_eq`, `mor_injective` (consequences of the
definition), `IsEquivalence.id` and `Examples.isEquivalence_pairToPoint` (witnesses).

`B` says that the project's `IsEquivalence` (and its class `EP.equivalences`) is the blind
author's `IsEquivB`: full and faithful in terms of the structure maps, a homeomorphism of the
blind author's own orbit spaces (`Quot`, quotient topology) inducing `|x| ↦ |F x|`, and a local
sc-diffeomorphism on objects.

* `A ⇒ B`: `full_iff` and `faithful_iff` from `A` translate (1); (2) is `IsHomeomorph` of the
  project's `orbitMap` iff a homeomorphism `e` with `e |x| = |F x|`: the project's orbit space
  `Quotient X.orbitSetoid` with Mathlib's quotient topology is definitionally the blind
  author's `Quot (IsoRelB X)` with the quotient topology, and `e` is then `orbitMap` (glue
  lemma `orbitHomeoB_iff`); (3) is `MPolyfold.IsLocalScDiffeo` unfolded (definitional).
* `B ⇒ A`: `full_iff`, `faithful_iff`, `essSurj_iff` are statements about arbitrary groupoids,
  not consequences of `B`; they are re-proved outright (`full_iff'` etc., copies of the
  project's proofs, using only non-item lemmas).  The other six conjuncts go through `B`:
  an equivalence is turned into `IsEquivB` and the consequences are read off it (`essSurj`,
  `exists_iso` from surjectivity of the blind homeomorphism), and `IsEquivalence.id`,
  `isEquivalence_pairToPoint` are obtained by proving `IsEquivB` for these functors and applying
  `B`.
-/

namespace RoundTrip.V10_1
open Polyfold CategoryTheory

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.GroupoidFunctor.full_iff.{0, 0}) ∧
  (type_of% @Polyfold.GroupoidFunctor.faithful_iff.{0, 0}) ∧
  (type_of% @Polyfold.GroupoidFunctor.essSurj_iff.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsEquivalence.essSurj.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsEquivalence.exists_iso.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsEquivalence.exists_mor_eq.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsEquivalence.mor_injective.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsEquivalence.id.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.Examples.isEquivalence_pairToPoint)

theorem A_holds : A :=
  ⟨@GroupoidFunctor.full_iff.{0, 0}, @GroupoidFunctor.faithful_iff.{0, 0},
    @GroupoidFunctor.essSurj_iff.{0, 0}, @EpFunctor.IsEquivalence.essSurj.{0, 0},
    @EpFunctor.IsEquivalence.exists_iso.{0, 0}, @EpFunctor.IsEquivalence.exists_mor_eq.{0, 0},
    @EpFunctor.IsEquivalence.mor_injective.{0, 0}, @EpFunctor.IsEquivalence.id.{0},
    @EpGroupoid.Examples.isEquivalence_pairToPoint⟩

/-! ### Glue -/

section Glue

variable {Obj Mor Obj' Mor' : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

/-- (2): the blind author's orbit homeomorphism is `IsHomeomorph` of the project's `orbitMap`
(the two orbit spaces are definitionally equal, with the same quotient topology). -/
theorem orbitHomeoB_iff (F : EpFunctor X Y) : OrbitHomeoB F ↔ IsHomeomorph F.orbitMap := by
  constructor
  · rintro ⟨e, he⟩
    have : (F.orbitMap : X.OrbitSpace → Y.OrbitSpace) = e := by
      funext a
      induction a using Quotient.inductionOn with | h x => exact (he x).symm
    rw [this]
    exact e.isHomeomorph
  · intro h
    exact ⟨h.homeomorph, fun _ => rfl⟩

/-- (3) is definitional. -/
theorem localScDiffeoObjB_iff (F : EpFunctor X Y) :
    LocalScDiffeoObjB F ↔ X.PObj.IsLocalScDiffeo Y.PObj F.obj := Iff.rfl

/-- The surjectivity of `|F|`, read off `IsEquivB`. -/
theorem exists_iso_of_isEquivB {F : EpFunctor X Y} (h : IsEquivB F) (y : Obj') :
    ∃ (x : Obj) (ψ : Mor'), Y.src ψ = F.obj x ∧ Y.tgt ψ = y := by
  obtain ⟨e, he⟩ := h.2.1
  obtain ⟨a, ha⟩ := e.surjective (Quot.mk _ y)
  induction a using Quot.ind with | mk x => ?_
  rw [he x] at ha
  have : Y.π (F.obj x) = Y.π y := ha
  obtain ⟨ψ, hs, ht⟩ := Y.π_eq_π_iff.1 this
  exact ⟨x, ψ, hs, ht⟩

end Glue

/-! ### Re-proofs of the three groupoid lemmas (copies of the project's proofs) -/

section Reproof

variable {Obj Mor Obj' Mor' : Type} {G : GroupoidStr Obj Mor} {H : GroupoidStr Obj' Mor'}

theorem full_iff' (F : GroupoidFunctor G H) : F.toFunctor.Full ↔
    ∀ (x x' : Obj) (ψ : Mor'), H.src ψ = F.obj x →
    H.tgt ψ = F.obj x' → ∃ φ, G.src φ = x ∧ G.tgt φ = x' ∧ F.mor φ = ψ := by
  constructor
  · intro h x x' ψ hs ht
    obtain ⟨f, hf⟩ := h.map_surjective (X := G.toOb x) (Y := G.toOb x') (H.homMk ψ hs ht)
    exact ⟨f.1, f.2.1, f.2.2, congrArg Subtype.val hf⟩
  · intro h
    refine ⟨fun {x x'} ψ => ?_⟩
    obtain ⟨φ, hs, ht, he⟩ := h x x' ψ.1 ψ.2.1 ψ.2.2
    exact ⟨G.homMk φ hs ht, Subtype.ext he⟩

theorem faithful_iff' (F : GroupoidFunctor G H) : F.toFunctor.Faithful ↔
    ∀ φ φ' : Mor, G.src φ = G.src φ' →
    G.tgt φ = G.tgt φ' → F.mor φ = F.mor φ' → φ = φ' := by
  constructor
  · intro h φ φ' hs ht he
    have := h.map_injective (X := G.toOb (G.src φ)) (Y := G.toOb (G.tgt φ))
      (a₁ := G.homMk φ rfl rfl) (a₂ := G.homMk φ' hs.symm ht.symm) (Subtype.ext he)
    exact congrArg Subtype.val this
  · intro h
    exact ⟨fun {_ _} f f' he => Subtype.ext (h f.1 f'.1 (f.2.1.trans f'.2.1.symm)
      (f.2.2.trans f'.2.2.symm) (congrArg Subtype.val he))⟩

theorem essSurj_iff' (F : GroupoidFunctor G H) : F.toFunctor.EssSurj ↔
    ∀ y : Obj', ∃ (x : Obj) (ψ : Mor'), H.src ψ = F.obj x ∧ H.tgt ψ = y := by
  constructor
  · intro h y
    obtain ⟨x, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage F.toFunctor (H.toOb y)
    exact ⟨x, i.hom.1, i.hom.2.1, i.hom.2.2⟩
  · intro h
    refine ⟨fun y => ?_⟩
    obtain ⟨x, ψ, hs, ht⟩ := h y
    exact ⟨x, ⟨(Groupoid.isoEquivHom (H.toOb (F.obj x)) (H.toOb y)).symm (H.homMk ψ hs ht)⟩⟩

end Reproof

/-! ### `A ⇒ B` -/

theorem A_to_B : A → B := by
  intro hA
  have key : ∀ (Obj Mor Obj' Mor' : Type) [TopologicalSpace Obj] [T2Space Obj]
      [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
      [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
      [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
      (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor') (F : EpFunctor X Y),
      F.IsEquivalence ↔ IsEquivB F := by
    intro Obj Mor Obj' Mor' _ _ _ _ _ _ _ _ _ _ _ _ X Y F
    have hfull := hA.1 F.toGroupoidFunctor
    have hfaith := hA.2.1 F.toGroupoidFunctor
    constructor
    · intro h
      exact ⟨⟨hfaith.1 h.faithful, hfull.1 h.full⟩, (orbitHomeoB_iff F).2 h.isHomeomorph_orbitMap,
        h.isLocalScDiffeo_obj⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨hfull.2 h2, hfaith.2 h1, (orbitHomeoB_iff F).1 h3, h4⟩
  exact ⟨key, fun A A' F => key A.Obj A.Mor A'.Obj A'.Mor A.X A'.X F⟩

/-! ### `B ⇒ A` -/

open EpGroupoid.Examples in
theorem B_to_A : B → A := by
  intro hB
  refine ⟨@full_iff', @faithful_iff', @essSurj_iff', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F hF
    exact (essSurj_iff' F.toGroupoidFunctor).2
      (exists_iso_of_isEquivB ((hB.1 _ _ _ _ X Y F).1 hF))
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F hF y
    exact exists_iso_of_isEquivB ((hB.1 _ _ _ _ X Y F).1 hF) y
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F hF x x' ψ hs ht
    exact ((hB.1 _ _ _ _ X Y F).1 hF).1.2 x x' ψ hs ht
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F hF φ φ' hs ht he
    exact ((hB.1 _ _ _ _ X Y F).1 hF).1.1 φ φ' hs ht he
  · intro Obj Mor _ _ _ _ _ _ X
    refine (hB.1 _ _ _ _ X X (EpFunctor.id X)).2 ⟨⟨fun _ _ _ _ h => h, fun _ _ ψ hs ht =>
      ⟨ψ, hs, ht, rfl⟩⟩, ⟨Homeomorph.refl _, fun _ => rfl⟩, ?_⟩
    exact MPolyfold.isLocalScDiffeo_id
  · refine (hB.1 _ _ _ _ _ _ pairToPoint).2 ⟨⟨fun φ φ' hs ht _ => Prod.ext ht hs,
      fun x x' _ _ _ => ⟨(x', x), rfl, rfl, rfl⟩⟩, ?_, isLocalScDiffeo_discrete _⟩
    refine ⟨{ toFun := fun _ => Quot.mk _ ()
              invFun := fun _ => Quot.mk _ 0
              left_inv := fun a => ?_
              right_inv := fun b => ?_
              continuous_toFun := continuous_const
              continuous_invFun := continuous_const }, fun _ => rfl⟩
    · induction a using Quot.ind with
      | mk x => exact Quot.sound ⟨(x, 0), rfl, rfl⟩
    · induction b using Quot.ind with
      | mk u => rfl

#rt_check RoundTrip.V10_1.A_to_B [Polyfold.GroupoidFunctor.full_iff,
  Polyfold.GroupoidFunctor.faithful_iff, Polyfold.GroupoidFunctor.essSurj_iff,
  Polyfold.EpFunctor.IsEquivalence.essSurj, Polyfold.EpFunctor.IsEquivalence.exists_iso,
  Polyfold.EpFunctor.IsEquivalence.exists_mor_eq, Polyfold.EpFunctor.IsEquivalence.mor_injective,
  Polyfold.EpFunctor.IsEquivalence.id, Polyfold.EpGroupoid.Examples.isEquivalence_pairToPoint]
#rt_check RoundTrip.V10_1.B_to_A [Polyfold.GroupoidFunctor.full_iff,
  Polyfold.GroupoidFunctor.faithful_iff, Polyfold.GroupoidFunctor.essSurj_iff,
  Polyfold.EpFunctor.IsEquivalence.essSurj, Polyfold.EpFunctor.IsEquivalence.exists_iso,
  Polyfold.EpFunctor.IsEquivalence.exists_mor_eq, Polyfold.EpFunctor.IsEquivalence.mor_injective,
  Polyfold.EpFunctor.IsEquivalence.id, Polyfold.EpGroupoid.Examples.isEquivalence_pairToPoint]
#rt_overlap RoundTrip.V10_1.B_to_A [Polyfold.GroupoidFunctor.full_iff,
  Polyfold.GroupoidFunctor.faithful_iff, Polyfold.GroupoidFunctor.essSurj_iff,
  Polyfold.EpFunctor.IsEquivalence.essSurj, Polyfold.EpFunctor.IsEquivalence.exists_iso,
  Polyfold.EpFunctor.IsEquivalence.exists_mor_eq, Polyfold.EpFunctor.IsEquivalence.mor_injective,
  Polyfold.EpFunctor.IsEquivalence.id, Polyfold.EpGroupoid.Examples.isEquivalence_pairToPoint]

end RoundTrip.V10_1
