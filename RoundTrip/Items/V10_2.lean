import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_2

/-!
Round trip for V10_2 (2021 Lemma 10.1.2, p. 462 (2017: Lemma 10.1, p. 334), and the remarks
around it: `|F|` bijective for an equivalence of categories, compositions of equivalences,
equivalences not invertible as functors).

`A` is the conjunction of the types of the ten listed theorems, universes at `0`:
`EpFunctor.lemma_10_1_2`, `isEquivalence_iff`, `IsEquivalence.isEquivalence_toFunctor`,
`IsEquivalence.comp`, `GroupoidFunctor.injective_orbitMap_of_full`, `surjective_orbitMap_iff`,
`bijective_orbitMap_of_isEquivalence`, `EpFunctor.continuous_orbitMap`, `isOpenMap_orbitMap`,
`Examples.not_exists_leftInverse_pairToPoint`.

`B` says (a) the lemma, with full, faithful, essentially surjective and the equivalence of
Definition 10.1.1 in the blind author's elementary terms, and (b) some equivalence `F` in `EP.{0}`
has no two-sided inverse maps on objects and morphisms.

* `A ⇒ B`: (a) the blind hypotheses give Mathlib's `Functor.IsEquivalence` of `F.toFunctor` (via
  the non-item lemmas `full_iff`, `faithful_iff`, `essSurj_iff`), `A`'s `lemma_10_1_2` gives the
  project's `IsEquivalence`, and the glue `isEquivB_of_isEquivalence` (the project's orbit space
  with the quotient topology is definitionally the blind `Quot`) gives `IsEquivB`.  (b) `F` is
  `pairToPoint` (pair groupoid of `ℤ` to the point): `IsEquivB` from `A`'s `lemma_10_1_2`, and
  an inverse `g₀` on objects would give the functor `G` (`g₀` on objects, identities on
  morphisms) excluded by `A`'s `not_exists_leftInverse_pairToPoint`.
* `B ⇒ A`: `lemma_10_1_2`, the backward half of `isEquivalence_iff` and `IsEquivalence.comp`
  come from `B` (a) (for `comp`: the composite is an equivalence of categories by Mathlib and a
  local sc-diffeomorphism by `IsLocalScDiffeo.comp`).  The forward half of `isEquivalence_iff`,
  `isEquivalence_toFunctor` (essential surjectivity read off the surjectivity of `|F|`), the
  orbit-map lemmas (statements about arbitrary groupoids, resp. any sc-smooth functor) and the
  non-invertibility of `pairToPoint` (a statement about a specific functor, not implied by the
  existential (b)) are not consequences of `B` and are re-proved outright from non-item lemmas.
-/

namespace RoundTrip.V10_2
open Polyfold CategoryTheory Function

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpFunctor.lemma_10_1_2.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.isEquivalence_iff.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsEquivalence.isEquivalence_toFunctor.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsEquivalence.comp.{0, 0, 0}) ∧
  (type_of% @Polyfold.GroupoidFunctor.injective_orbitMap_of_full.{0, 0}) ∧
  (type_of% @Polyfold.GroupoidFunctor.surjective_orbitMap_iff.{0, 0}) ∧
  (type_of% @Polyfold.GroupoidFunctor.bijective_orbitMap_of_isEquivalence.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.continuous_orbitMap.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.isOpenMap_orbitMap.{0, 0}) ∧
  (type_of% @Polyfold.EpGroupoid.Examples.not_exists_leftInverse_pairToPoint)

theorem A_holds : A :=
  ⟨@EpFunctor.lemma_10_1_2.{0, 0}, @EpFunctor.isEquivalence_iff.{0, 0},
    @EpFunctor.IsEquivalence.isEquivalence_toFunctor.{0, 0},
    @EpFunctor.IsEquivalence.comp.{0, 0, 0}, @GroupoidFunctor.injective_orbitMap_of_full.{0, 0},
    @GroupoidFunctor.surjective_orbitMap_iff.{0, 0},
    @GroupoidFunctor.bijective_orbitMap_of_isEquivalence.{0, 0},
    @EpFunctor.continuous_orbitMap.{0, 0}, @EpFunctor.isOpenMap_orbitMap.{0, 0},
    @EpGroupoid.Examples.not_exists_leftInverse_pairToPoint⟩

/-! ### Glue -/

section Glue

variable {Obj Mor Obj' Mor' : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

/-- The blind orbit homeomorphism is `IsHomeomorph` of the project's `orbitMap` (the orbit spaces
are definitionally equal, with the same quotient topology). -/
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

theorem fullyFaithfulB_iff (F : EpFunctor X Y) :
    FullyFaithfulB F ↔ F.toFunctor.Faithful ∧ F.toFunctor.Full :=
  ⟨fun h => ⟨(GroupoidFunctor.faithful_iff _).2 h.1, (GroupoidFunctor.full_iff _).2 h.2⟩,
    fun h => ⟨(GroupoidFunctor.faithful_iff _).1 h.1, (GroupoidFunctor.full_iff _).1 h.2⟩⟩

theorem isEquivB_of_isEquivalence {F : EpFunctor X Y} (h : F.IsEquivalence) : IsEquivB F :=
  ⟨(fullyFaithfulB_iff F).2 ⟨h.faithful, h.full⟩, (orbitHomeoB_iff F).2 h.isHomeomorph_orbitMap,
    h.isLocalScDiffeo_obj⟩

theorem isEquivalence_of_isEquivB {F : EpFunctor X Y} (h : IsEquivB F) : F.IsEquivalence :=
  ⟨((fullyFaithfulB_iff F).1 h.1).2, ((fullyFaithfulB_iff F).1 h.1).1,
    (orbitHomeoB_iff F).1 h.2.1, h.2.2⟩

/-- An equivalence is essentially surjective (re-proved: `|F|` is surjective). -/
theorem essSurj_of_isEquivalence {F : EpFunctor X Y} (h : F.IsEquivalence) :
    F.toFunctor.EssSurj := by
  refine (GroupoidFunctor.essSurj_iff _).2 fun y => ?_
  obtain ⟨a, ha⟩ := h.isHomeomorph_orbitMap.surjective (Y.π y)
  induction a using Quotient.inductionOn with | h x => ?_
  obtain ⟨ψ, hs, ht⟩ := Y.π_eq_π_iff.1 ha
  exact ⟨x, ψ, hs, ht⟩

end Glue

/-! ### `A ⇒ B` -/

open EpGroupoid.Examples in
theorem A_to_B : A → B := by
  intro hA
  refine ⟨?_, ?_⟩
  · intro Obj Mor Obj' Mor' _ _ _ _ _ _ _ _ _ _ _ _ X Y F hloc hff hes
    have hF : F.toFunctor.IsEquivalence :=
      { faithful := ((fullyFaithfulB_iff F).1 hff).1
        full := ((fullyFaithfulB_iff F).1 hff).2
        essSurj := (GroupoidFunctor.essSurj_iff _).2 hes }
    exact isEquivB_of_isEquivalence (hA.1 F hF hloc)
  · refine ⟨⟨ℤ, ℤ × ℤ, pairEpGroupoid⟩, ⟨Unit, Unit, pointEpGroupoid⟩, pairToPoint, ?_, ?_⟩
    · refine isEquivB_of_isEquivalence (hA.1 pairToPoint ?_ (isLocalScDiffeo_discrete _))
      exact
        { faithful := (GroupoidFunctor.faithful_iff _).2 fun _ _ hs ht _ => Prod.ext ht hs
          full := (GroupoidFunctor.full_iff _).2 fun x x' _ _ _ => ⟨(x', x), rfl, rfl, rfl⟩
          essSurj := (GroupoidFunctor.essSurj_iff _).2 fun _ => ⟨0, (), rfl, rfl⟩ }
    · rintro ⟨g₀, -, h1, -, -, -⟩
      let G : EpFunctor pointEpGroupoid pairEpGroupoid :=
        { obj := g₀
          mor := fun _ => pairEpGroupoid.unit (g₀ ())
          src_mor := fun _ => rfl
          tgt_mor := fun _ => rfl
          mor_comp := fun _ _ _ => rfl
          mor_unit := fun _ => rfl
          isScSmoothMap_obj := isScSmoothMap_discrete_of_continuous continuous_of_discreteTopology
          isScSmoothMap_mor := isScSmoothMap_const_discrete _ }
      exact hA.2.2.2.2.2.2.2.2.2 ⟨G, h1⟩

/-! ### `B ⇒ A` -/

open EpGroupoid.Examples in
theorem B_to_A : B → A := by
  intro hB
  have lem : ∀ {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj]
      [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
      {Obj' Mor' : Type} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
      [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
      {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (F : EpFunctor X Y),
      F.toFunctor.IsEquivalence → X.PObj.IsLocalScDiffeo Y.PObj F.obj → F.IsEquivalence := by
    intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F hF h
    exact isEquivalence_of_isEquivB (hB.1 _ _ _ _ X Y F h
      ((fullyFaithfulB_iff F).2 ⟨hF.faithful, hF.full⟩)
      ((GroupoidFunctor.essSurj_iff _).1 hF.essSurj))
  have toF : ∀ {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj]
      [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
      {Obj' Mor' : Type} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
      [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
      {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {F : EpFunctor X Y},
      F.IsEquivalence → F.toFunctor.IsEquivalence := fun h =>
    { faithful := h.faithful, full := h.full, essSurj := essSurj_of_isEquivalence h }
  have hinj : ∀ {Obj Mor Obj' Mor' : Type} {G : GroupoidStr Obj Mor}
      {H : GroupoidStr Obj' Mor'} (F : GroupoidFunctor G H), F.toFunctor.Full →
      Injective F.orbitMap := by
    intro Obj Mor Obj' Mor' G H F hF a b hab
    induction a using Quotient.inductionOn with | h x => ?_
    induction b using Quotient.inductionOn with | h x' => ?_
    change H.π (F.obj x) = H.π (F.obj x') at hab
    obtain ⟨ψ, hs, ht⟩ := H.π_eq_π_iff.1 hab
    obtain ⟨φ, hφs, hφt, -⟩ := (F.full_iff.1 hF) x x' ψ hs ht
    exact G.π_eq_π_iff.2 ⟨φ, hφs, hφt⟩
  have hsurj : ∀ {Obj Mor Obj' Mor' : Type} {G : GroupoidStr Obj Mor}
      {H : GroupoidStr Obj' Mor'} (F : GroupoidFunctor G H),
      Surjective F.orbitMap ↔ F.toFunctor.EssSurj := by
    intro Obj Mor Obj' Mor' G H F
    rw [GroupoidFunctor.essSurj_iff]
    constructor
    · intro h y
      obtain ⟨a, ha⟩ := h (H.π y)
      induction a using Quotient.inductionOn with | h x => ?_
      obtain ⟨ψ, hs, ht⟩ := H.π_eq_π_iff.1 ha
      exact ⟨x, ψ, hs, ht⟩
    · intro h b
      induction b using Quotient.inductionOn with | h y => ?_
      obtain ⟨x, ψ, hs, ht⟩ := h y
      exact ⟨G.π x, H.π_eq_π_iff.2 ⟨ψ, hs, ht⟩⟩
  refine ⟨@lem, fun F => ⟨fun h => ⟨toF h, h.isLocalScDiffeo_obj⟩, fun h => lem F h.1 h.2⟩,
    @toF, ?_, @hinj, @hsurj, fun F hF => ⟨hinj F hF.full, (hsurj F).2 hF.essSurj⟩, ?_, ?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ Obj'' Mor'' _ _ _ _ _ _ X Y Z G F hG hF
    have := toF hG
    have := toF hF
    have h3 : (G.comp F).toFunctor.IsEquivalence :=
      (inferInstance : (F.toFunctor ⋙ G.toFunctor).IsEquivalence)
    exact lem (G.comp F) h3 (hG.isLocalScDiffeo_obj.comp hF.isLocalScDiffeo_obj)
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F
    exact X.proposition_7_1_isOpenQuotientMap.isQuotientMap.continuous_iff.2
      (Y.continuous_π.comp F.continuous_obj')
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F h O hO
    have he : F.orbitMap '' O = Y.π '' (F.obj '' (X.π ⁻¹' O)) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨x, rfl⟩ := X.surjective_π w
        exact ⟨F.obj x, ⟨x, hw, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨X.π x, hx, rfl⟩
    rw [he]
    exact Y.proposition_7_1 _ (h _ (hO.preimage X.continuous_π))
  · rintro ⟨G, hG⟩
    have h := (hG 0).symm.trans (hG 1)
    exact absurd h (by decide)

#rt_check RoundTrip.V10_2.A_to_B [Polyfold.EpFunctor.lemma_10_1_2,
  Polyfold.EpFunctor.isEquivalence_iff, Polyfold.EpFunctor.IsEquivalence.isEquivalence_toFunctor,
  Polyfold.EpFunctor.IsEquivalence.comp, Polyfold.GroupoidFunctor.injective_orbitMap_of_full,
  Polyfold.GroupoidFunctor.surjective_orbitMap_iff,
  Polyfold.GroupoidFunctor.bijective_orbitMap_of_isEquivalence,
  Polyfold.EpFunctor.continuous_orbitMap, Polyfold.EpFunctor.isOpenMap_orbitMap,
  Polyfold.EpGroupoid.Examples.not_exists_leftInverse_pairToPoint]
#rt_check RoundTrip.V10_2.B_to_A [Polyfold.EpFunctor.lemma_10_1_2,
  Polyfold.EpFunctor.isEquivalence_iff, Polyfold.EpFunctor.IsEquivalence.isEquivalence_toFunctor,
  Polyfold.EpFunctor.IsEquivalence.comp, Polyfold.GroupoidFunctor.injective_orbitMap_of_full,
  Polyfold.GroupoidFunctor.surjective_orbitMap_iff,
  Polyfold.GroupoidFunctor.bijective_orbitMap_of_isEquivalence,
  Polyfold.EpFunctor.continuous_orbitMap, Polyfold.EpFunctor.isOpenMap_orbitMap,
  Polyfold.EpGroupoid.Examples.not_exists_leftInverse_pairToPoint]
#rt_overlap RoundTrip.V10_2.B_to_A [Polyfold.EpFunctor.lemma_10_1_2,
  Polyfold.EpFunctor.isEquivalence_iff, Polyfold.EpFunctor.IsEquivalence.isEquivalence_toFunctor,
  Polyfold.EpFunctor.IsEquivalence.comp, Polyfold.GroupoidFunctor.injective_orbitMap_of_full,
  Polyfold.GroupoidFunctor.surjective_orbitMap_iff,
  Polyfold.GroupoidFunctor.bijective_orbitMap_of_isEquivalence,
  Polyfold.EpFunctor.continuous_orbitMap, Polyfold.EpFunctor.isOpenMap_orbitMap,
  Polyfold.EpGroupoid.Examples.not_exists_leftInverse_pairToPoint]

end RoundTrip.V10_2
