import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_9

/-! Round trip for V10_9 (2021 Remark 10.1.12, p. 472, new in the 2021 edition: for an
equivalence `F` and `ψ : F(x) → y`, `g ↦ ψ ∘ F(g) ∘ ψ⁻¹` is an isomorphism `G_x → G_y` mapping
`T_x` onto `T_y`).

The item lists the definition `EpFunctor.isotropyHom` (vocabulary, `g ↦ F(g)`, `G_x → G_{F x}`)
and three theorems; `A` is the conjunction of their types, universes at `0`:
* `isotropyHom_mem_trivialSet_iff`: for `F` a *local sc-diffeomorphism on objects* (not
  necessarily an equivalence), `F(g) ∈ T_{F x} ↔ g ∈ T_x`;
* `IsEquivalence.bijective_isotropyHom`: for an equivalence, `G_x → G_{F x}` is bijective;
* `IsEquivalence.remark_10_1_12`: the remark, with value `(ψ ∘ F(g)) ∘ ψ⁻¹` and
  `e g ∈ T_y ↔ g ∈ T_x`.

`B` is the remark with B's own Definition 10.1.1 (`IsEquivB`), value `ψ ∘ (F(g) ∘ ψ⁻¹)` and
`trivialSubgroup` (whose carrier is `trivialSet`, `mem_trivialSubgroup` is `Iff.rfl`).

* Glue `isEquivB_iff`: `IsEquivB F ↔ F.IsEquivalence` (as in `RoundTrip/Items/V10_7.lean`).
* `A_to_B`: `remark_10_1_12`, re-associating the composition (`GroupoidStr.comp_assoc`).
* `B_to_A`: `remark_10_1_12` from `B` (re-associating); `bijective_isotropyHom` from `B` with
  `y = F x`, `ψ = 1_{F x}` (then `c g = 1 ∘ F(g) ∘ 1⁻¹ = F(g)`, so `isotropyHom = c`).
  `isotropyHom_mem_trivialSet_iff` is about all local sc-diffeomorphisms on objects, which `B`
  (about equivalences only) does not cover; it is re-proved outright (the project's proof,
  copied, from the non-item lemmas `mor_mem_nonEffectivePart`, `mem_nonEffectivePart_of_mor`,
  `val_mem_nonEffectivePart_iff`).
-/

namespace RoundTrip.V10_9
open Polyfold

universe u v

section Glue

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']

/-- B's Definition 10.1.1 is the project's `EpFunctor.IsEquivalence`. -/
theorem isEquivB_iff {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (F : EpFunctor X Y) :
    IsEquivB F ↔ F.IsEquivalence := by
  constructor
  · rintro ⟨⟨hfaith, hfull⟩, ⟨e, he⟩, hloc⟩
    have hfun : (fun q : X.OrbitSpace => (e q : Y.OrbitSpace)) = F.orbitMap := by
      funext q
      induction q using Quot.ind with | mk x => exact he x
    refine ⟨(GroupoidFunctor.full_iff _).2 hfull, (GroupoidFunctor.faithful_iff _).2 hfaith,
      ?_, hloc⟩
    rw [← hfun]
    exact e.isHomeomorph
  · intro h
    exact ⟨⟨(GroupoidFunctor.faithful_iff _).1 h.faithful, (GroupoidFunctor.full_iff _).1 h.full⟩,
      ⟨h.isHomeomorph_orbitMap.homeomorph, fun _ => rfl⟩, h.isLocalScDiffeo_obj⟩

end Glue

/-- The project's statement (universes at `0`), one definition per theorem. -/
def A1 : Prop := type_of% @Polyfold.EpFunctor.isotropyHom_mem_trivialSet_iff.{0, 0}
def A2 : Prop := type_of% @Polyfold.EpFunctor.IsEquivalence.bijective_isotropyHom.{0, 0}
def A3 : Prop := type_of% @Polyfold.EpFunctor.IsEquivalence.remark_10_1_12.{0, 0}

/-- The project's statement. -/
def A : Prop := A1 ∧ A2 ∧ A3

theorem A_holds : A :=
  ⟨@Polyfold.EpFunctor.isotropyHom_mem_trivialSet_iff.{0, 0},
    @Polyfold.EpFunctor.IsEquivalence.bijective_isotropyHom.{0, 0},
    @Polyfold.EpFunctor.IsEquivalence.remark_10_1_12.{0, 0}⟩

theorem A_to_B : A → B := by
  rintro ⟨-, -, h3⟩
  intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F hF x y ψ hs ht
  obtain ⟨e, hval, hmem⟩ := h3 ((isEquivB_iff F).1 hF) ψ hs ht
  refine ⟨e, fun g => ?_, fun g => (hmem g).symm⟩
  rw [hval, Y.comp_assoc _ _ _ (by rw [F.tgt_mor, g.tgt_val, hs]) (by rw [Y.tgt_inv, F.src_mor,
    g.src_val, hs])]

/-- **Re-proved outright** (the project's proof): `F(g) ∈ T_{F x} ↔ g ∈ T_x` for `F` a local
sc-diffeomorphism on objects. -/
theorem isotropyHom_mem_trivialSet_iff' : A1 := by
  intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F hF x g
  rw [← EpGroupoid.val_mem_nonEffectivePart_iff, ← EpGroupoid.val_mem_nonEffectivePart_iff,
    EpFunctor.isotropyHom_val]
  exact ⟨F.mem_nonEffectivePart_of_mor hF (g.src_val.trans g.tgt_val.symm),
    F.mor_mem_nonEffectivePart hF⟩

theorem B_to_A : B → A := by
  intro hB
  have h3 : A3 := by
    intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F hF x y ψ hs ht
    obtain ⟨c, hval, hmem⟩ := hB Obj Mor Obj' Mor' X Y F ((isEquivB_iff F).2 hF) x y ψ hs ht
    refine ⟨c, fun g => ?_, fun g => (hmem g).symm⟩
    rw [hval, Y.comp_assoc _ _ _ (by rw [F.tgt_mor, g.tgt_val, hs]) (by rw [Y.tgt_inv, F.src_mor,
      g.src_val, hs])]
  have h2 : A2 := by
    intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F hF x
    obtain ⟨c, hval, -⟩ := hB Obj Mor Obj' Mor' X Y F ((isEquivB_iff F).2 hF) x (F.obj x)
      (Y.unit (F.obj x)) (Y.src_unit _) (Y.tgt_unit _)
    have he : (F.isotropyHom x : X.Isotropy x → Y.Isotropy (F.obj x)) = c := by
      funext g
      refine GroupoidStr.Isotropy.ext ?_
      rw [hval, EpFunctor.isotropyHom_val, GroupoidStr.inv_unit,
        GroupoidStr.comp_unit_of_eq (by rw [F.src_mor, g.src_val]),
        GroupoidStr.unit_comp_of_eq (by rw [F.tgt_mor, g.tgt_val])]
    rw [he]
    exact c.bijective
  exact ⟨isotropyHom_mem_trivialSet_iff', h2, h3⟩

#rt_check RoundTrip.V10_9.A_to_B [Polyfold.EpFunctor.isotropyHom_mem_trivialSet_iff,
  Polyfold.EpFunctor.IsEquivalence.bijective_isotropyHom,
  Polyfold.EpFunctor.IsEquivalence.remark_10_1_12]
#rt_check RoundTrip.V10_9.B_to_A [Polyfold.EpFunctor.isotropyHom_mem_trivialSet_iff,
  Polyfold.EpFunctor.IsEquivalence.bijective_isotropyHom,
  Polyfold.EpFunctor.IsEquivalence.remark_10_1_12]
#rt_overlap RoundTrip.V10_9.B_to_A [Polyfold.EpFunctor.isotropyHom_mem_trivialSet_iff,
  Polyfold.EpFunctor.IsEquivalence.bijective_isotropyHom,
  Polyfold.EpFunctor.IsEquivalence.remark_10_1_12]

end RoundTrip.V10_9
