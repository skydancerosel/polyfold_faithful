import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_11

/-! Round trip for V10_11 (2021 Proposition 10.1.14, p. 473; 2017: Proposition 10.5, p. 341: for
an equivalence `F` with `𝐗^R`, `𝐘^R` Hausdorff, `F_R : X_R → Y_R` is a well-defined sc-smooth
functor and an equivalence).

The item lists the definitions `EpFunctor.reducedGroupoidFunctor`, `EpFunctor.reduced`
(vocabulary: `F_R = F` on objects, `F_R [φ] = [F φ]`, made an `EpFunctor` by
`EpFunctor.ofContinuous`) and two theorems; `A` is the conjunction of their types, universes at
`0`:
* `reducedπ_eq_of_mor`: for an equivalence `F` (no Hausdorff hypothesis), `φ, φ'` with the same
  source and target and `[F φ] = [F φ']` have `[φ] = [φ']` (faithfulness of `F_R`);
* `proposition_10_1_14`: with `[T2Space X.ReducedMor] [T2Space Y.ReducedMor]`, `F.reduced` is an
  equivalence.

`B`: with the same Hausdorff instances, for B's own Definition 10.1.1 (`IsEquivB`), there is an
`EpFunctor X_R → Y_R` equal to `F` on objects, to `[φ] ↦ [F φ]` on morphisms, and an equivalence.

* Glue `isEquivB_iff`: `IsEquivB F ↔ F.IsEquivalence` (as in `RoundTrip/Items/V10_7.lean`).
* `A_to_B`: `F_R = F.reduced _` (the two equations are `rfl`), an equivalence by
  `proposition_10_1_14`.
* `B_to_A`: `proposition_10_1_14` from `B` (`B`'s functor equals `F.reduced _` by
  `EpFunctor.ext` and `Quot.ind`).  `reducedπ_eq_of_mor` is stated without the Hausdorff
  hypotheses, so `B` (which needs them to even form `X_R`) does not give it; it is re-proved
  outright (the project's proof, copied, from the non-item lemmas `reducedπ_eq_iff_comp_inv`,
  `mem_nonEffectivePart_of_mor`).
-/

namespace RoundTrip.V10_11
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
def A1 : Prop := type_of% @Polyfold.EpFunctor.reducedπ_eq_of_mor.{0, 0}
def A2 : Prop := type_of% @Polyfold.EpFunctor.proposition_10_1_14.{0, 0}

/-- The project's statement. -/
def A : Prop := A1 ∧ A2

theorem A_holds : A :=
  ⟨@Polyfold.EpFunctor.reducedπ_eq_of_mor.{0, 0}, @Polyfold.EpFunctor.proposition_10_1_14.{0, 0}⟩

theorem A_to_B : A → B := by
  rintro ⟨-, h2⟩
  intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F _ _ hF
  have hF' := (isEquivB_iff F).1 hF
  exact ⟨F.reduced hF'.isLocalScDiffeo_obj, fun _ => rfl, fun _ => rfl,
    (isEquivB_iff _).2 (h2 hF')⟩

/-- **Re-proved outright** (the project's proof): `reducedπ_eq_of_mor`. -/
theorem reducedπ_eq_of_mor' : A1 := by
  intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F hF φ φ' hs ht h
  obtain ⟨-, hk⟩ := Y.reducedπ_eq_iff_comp_inv.1 h
  have hc : X.src (X.inv φ') = X.tgt φ := by rw [X.src_inv, ht]
  rw [← F.mor_inv, ← F.mor_comp _ _ hc] at hk
  refine X.reducedπ_eq_iff_comp_inv.2 ⟨ht, F.mem_nonEffectivePart_of_mor
    hF.isLocalScDiffeo_obj ?_ hk⟩
  rw [X.src_comp _ _ hc, X.tgt_comp _ _ hc, X.tgt_inv, hs]

theorem B_to_A : B → A := by
  intro hB
  refine ⟨reducedπ_eq_of_mor', ?_⟩
  intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y _ _ F hF
  obtain ⟨FR, hobj, hmor, hFR⟩ := hB Obj Mor Obj' Mor' X Y F ((isEquivB_iff F).2 hF)
  have he : FR = F.reduced hF.isLocalScDiffeo_obj := by
    refine EpFunctor.ext (funext hobj) (funext fun q => ?_)
    induction q using Quot.ind with | mk φ => exact hmor φ
  rw [← he]
  exact (isEquivB_iff FR).1 hFR

#rt_check RoundTrip.V10_11.A_to_B [Polyfold.EpFunctor.reducedπ_eq_of_mor,
  Polyfold.EpFunctor.proposition_10_1_14]
#rt_check RoundTrip.V10_11.B_to_A [Polyfold.EpFunctor.reducedπ_eq_of_mor,
  Polyfold.EpFunctor.proposition_10_1_14]
#rt_overlap RoundTrip.V10_11.B_to_A [Polyfold.EpFunctor.reducedπ_eq_of_mor,
  Polyfold.EpFunctor.proposition_10_1_14]

end RoundTrip.V10_11
