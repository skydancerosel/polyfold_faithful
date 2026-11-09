import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_5

/-!
Round trip for V10_5 (2021 Proposition 10.1.5, p. 464 (2017: Proposition 10.2, p. 336):
naturally equivalent functors, one an equivalence, the other one too).

`A` is the conjunction of the types of the five listed theorems, universes at `0`:
`EpFunctor.proposition_10_1_5` (`F ≃ G ⇒ (F equivalence ↔ G equivalence)`),
`IsEquivalence.of_natTrans`, and the lemmas `EpNatTrans.continuous_app`,
`EpNatTrans.isLocalScDiffeo_app` (`τ : X → 𝐘` is a local sc-diffeomorphism if `F` is one on
objects), `EpNatTrans.isLocalScDiffeo_obj` (then so is `G`).

`B`: for `F ≃ G` in the blind author's sense (`NatEqB`), `IsEquivB F ↔ IsEquivB G` (both
implications).

* `A ⇒ B`: a blind natural transformation is an `EpNatTrans` (its fields; naturality with
  `x = s φ`, `x' = t φ`), so `F.NaturallyEquivalent G`, and `A`'s `proposition_10_1_5` gives the
  iff, transported to `IsEquivB` by the glue (the project's orbit space with the quotient topology
  is definitionally the blind `Quot`; `full_iff`, `faithful_iff` for (1)).
* `B ⇒ A`: `proposition_10_1_5` and `of_natTrans` from `B` (an `EpNatTrans` gives `NatEqB`).  The
  three lemmas on `τ` are not consequences of `B` (they assume only that `F` is a local
  sc-diffeomorphism on objects, not an equivalence) and are re-proved outright, copying the
  project's proofs (`IsLocalScDiffeoAt.of_comp_left`, `comp`, `congr`, non-item lemmas).
-/

namespace RoundTrip.V10_5
open Polyfold CategoryTheory Filter

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpFunctor.proposition_10_1_5.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsEquivalence.of_natTrans.{0, 0}) ∧
  (type_of% @Polyfold.EpNatTrans.continuous_app.{0, 0}) ∧
  (type_of% @Polyfold.EpNatTrans.isLocalScDiffeo_app.{0, 0}) ∧
  (type_of% @Polyfold.EpNatTrans.isLocalScDiffeo_obj.{0, 0})

theorem A_holds : A :=
  ⟨@EpFunctor.proposition_10_1_5.{0, 0}, @EpFunctor.IsEquivalence.of_natTrans.{0, 0},
    @EpNatTrans.continuous_app.{0, 0}, @EpNatTrans.isLocalScDiffeo_app.{0, 0},
    @EpNatTrans.isLocalScDiffeo_obj.{0, 0}⟩

/-! ### Glue -/

section Glue

variable {Obj Mor Obj' Mor' : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

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

theorem isEquivB_iff (F : EpFunctor X Y) : IsEquivB F ↔ F.IsEquivalence :=
  ⟨fun h => ⟨(GroupoidFunctor.full_iff _).2 h.1.2, (GroupoidFunctor.faithful_iff _).2 h.1.1,
      (orbitHomeoB_iff F).1 h.2.1, h.2.2⟩,
    fun h => ⟨⟨(GroupoidFunctor.faithful_iff _).1 h.faithful,
      (GroupoidFunctor.full_iff _).1 h.full⟩, (orbitHomeoB_iff F).2 h.isHomeomorph_orbitMap,
      h.isLocalScDiffeo_obj⟩⟩

theorem natEqB_iff (F G : EpFunctor X Y) : NatEqB F G ↔ F.NaturallyEquivalent G := by
  constructor
  · rintro ⟨τ, h1, h2, h3⟩
    exact ⟨{ app := τ
             isScSmoothMap_app := h1
             src_app := fun x => (h2 x).1
             tgt_app := fun x => (h2 x).2
             naturality := fun φ => h3 φ _ _ rfl rfl }⟩
  · rintro ⟨τ⟩
    refine ⟨τ.app, τ.isScSmoothMap_app, fun x => ⟨τ.src_app x, τ.tgt_app x⟩, ?_⟩
    rintro φ x x' rfl rfl
    exact τ.naturality φ

end Glue

/-! ### `A ⇒ B` -/

theorem A_to_B : A → B := by
  intro hA Obj Mor Obj' Mor' _ _ _ _ _ _ _ _ _ _ _ _ X Y F G h
  have hiff := hA.1 ((natEqB_iff F G).1 h)
  exact ⟨fun hF => (isEquivB_iff G).2 (hiff.1 ((isEquivB_iff F).1 hF)),
    fun hG => (isEquivB_iff F).2 (hiff.2 ((isEquivB_iff G).1 hG))⟩

/-! ### `B ⇒ A` -/

theorem B_to_A : B → A := by
  intro hB
  have happ : ∀ {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
      {Obj' Mor' : Type} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
      [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
      {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {F G : EpFunctor X Y}
      (τ : EpNatTrans F G), X.PObj.IsLocalScDiffeo Y.PObj F.obj →
      X.PObj.IsLocalScDiffeo Y.PMor τ.app := by
    intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F G τ h x
    exact MPolyfold.IsLocalScDiffeoAt.of_comp_left (Y.isLocalScDiffeo_src.at (τ.app x))
      (continuousOn_univ.1 τ.isScSmoothMap_app.continuousOn)
      ((h.at x).congr (Eventually.of_forall fun z => (τ.src_app z).symm))
  refine ⟨?_, ?_, ?_, @happ, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F G h
    have hb := hB Obj Mor Obj' Mor' X Y F G ((natEqB_iff F G).2 h)
    exact ⟨fun hF => (isEquivB_iff G).1 (hb.1 ((isEquivB_iff F).2 hF)),
      fun hG => (isEquivB_iff F).1 (hb.2 ((isEquivB_iff G).2 hG))⟩
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F G τ hF
    exact (isEquivB_iff G).1
      ((hB Obj Mor Obj' Mor' X Y F G ((natEqB_iff F G).2 ⟨τ⟩)).1 ((isEquivB_iff F).2 hF))
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F G τ
    exact continuousOn_univ.1 τ.isScSmoothMap_app.continuousOn
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F G τ h x
    exact (MPolyfold.IsLocalScDiffeoAt.comp (Y.isLocalScDiffeo_tgt.at (τ.app x))
      ((happ τ h).at x)).congr (Eventually.of_forall fun z => τ.tgt_app z)

#rt_check RoundTrip.V10_5.A_to_B [Polyfold.EpFunctor.proposition_10_1_5,
  Polyfold.EpFunctor.IsEquivalence.of_natTrans, Polyfold.EpNatTrans.continuous_app,
  Polyfold.EpNatTrans.isLocalScDiffeo_app, Polyfold.EpNatTrans.isLocalScDiffeo_obj]
#rt_check RoundTrip.V10_5.B_to_A [Polyfold.EpFunctor.proposition_10_1_5,
  Polyfold.EpFunctor.IsEquivalence.of_natTrans, Polyfold.EpNatTrans.continuous_app,
  Polyfold.EpNatTrans.isLocalScDiffeo_app, Polyfold.EpNatTrans.isLocalScDiffeo_obj]
#rt_overlap RoundTrip.V10_5.B_to_A [Polyfold.EpFunctor.proposition_10_1_5,
  Polyfold.EpFunctor.IsEquivalence.of_natTrans, Polyfold.EpNatTrans.continuous_app,
  Polyfold.EpNatTrans.isLocalScDiffeo_app, Polyfold.EpNatTrans.isLocalScDiffeo_obj]

end RoundTrip.V10_5
