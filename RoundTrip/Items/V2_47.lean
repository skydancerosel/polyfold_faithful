import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_47

/-! Round trip for V2_47 (Corollary 2.41: a tame retract is face-structured).

`A` is the conjunction of the types of `Polyfold.corollary_2_41`, `Polyfold.corollary_2_41_retract`
and `Polyfold.LocalModel.isFaceStructured_toMPolyfold` (no universe parameters).

`A → B`: `corollary_2_41` for the local model `(O, C, E)`, unfolding `IsFaceStructured`.

`B → A`: `corollary_2_41` is `B` (after `cases` on the local model); the version with a retraction
tame for one presentation follows through `IsTameWith.isTame`; the version in `E₀`
(`corollary_2_41_retract`, faces `IsRetractFace` of the retract) is transferred from `B` for the
local model `R.toLocalModel` through `LocalModel.isFace_toMPolyfold_iff` (Lemma 2.40's transfer
lemma, item V2_46, not banned here) and `d_O = d_C` (Proposition 2.36). -/

namespace RoundTrip.V2_47
open Polyfold Set

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.corollary_2_41) ∧ (type_of% @Polyfold.corollary_2_41_retract) ∧
    (type_of% @Polyfold.LocalModel.isFaceStructured_toMPolyfold)

theorem A_holds : A :=
  ⟨@Polyfold.corollary_2_41, @Polyfold.corollary_2_41_retract,
    @Polyfold.LocalModel.isFaceStructured_toMPolyfold⟩

theorem A_to_B : A → B := by
  intro hA E C O hO hne htame x
  exact hA.1 ⟨E, C, O, hO⟩ hne htame x

/-- `B` for a local model. -/
theorem B_model (hB : B) (M : LocalModel) (hne : M.O.Nonempty)
    (htame : IsTameRetract M.E M.C M.O) : (M.toMPolyfold hne).IsFaceStructured := by
  cases M with
  | mk E C O hO => exact hB E C O hO hne htame

theorem B_to_A : B → A := by
  intro hB
  refine ⟨B_model hB, ?_, ?_⟩
  · -- `corollary_2_41_retract`
    intro E n W C R T hT hR x hx
    classical
    set M : LocalModel := R.toLocalModel with hM
    have hMO : M.O = R.retract := rfl
    have hMC : M.C = C := rfl
    have hne : M.O.Nonempty := ⟨x, hx⟩
    have htame : IsTameRetract M.E M.C M.O := ⟨R, rfl, hR.isTame hT⟩
    have hFS := B_model hB M hne htame ⟨x, hx⟩
    have hd := M.degIndex_toMPolyfold_of_isTameWith hne R rfl hT hR
    have hinj : InjOn (fun F : Set M.O => Subtype.val '' F)
        {F | (M.toMPolyfold hne).IsFace F ∧ (⟨x, hx⟩ : M.O) ∈ F} :=
      (Set.image_injective.2 Subtype.val_injective).injOn
    have himage : (fun F : Set M.O => Subtype.val '' F) ''
        {F | (M.toMPolyfold hne).IsFace F ∧ (⟨x, hx⟩ : M.O) ∈ F} =
          {G | R.IsRetractFace G ∧ x ∈ G} := by
      ext G
      constructor
      · rintro ⟨F, ⟨hF, hxF⟩, rfl⟩
        exact ⟨(M.isFace_toMPolyfold_iff hne R rfl hT hR F).1 hF, ⟨⟨x, hx⟩, hxF, rfl⟩⟩
      · rintro ⟨hG, hxG⟩
        have hGO : G ⊆ M.O := by
          obtain ⟨_, _, rfl⟩ := hG; exact inter_subset_right
        have himg : Subtype.val '' (Subtype.val ⁻¹' G : Set M.O) = G := by
          rw [Subtype.image_preimage_coe, inter_eq_right.2 hGO]
        refine ⟨Subtype.val ⁻¹' G, ⟨?_, hxG⟩, himg⟩
        rw [M.isFace_toMPolyfold_iff hne R rfl hT hR, himg]
        exact hG
    exact ((congrArg Set.encard himage).symm.trans hinj.encard_image).trans
      (hFS.trans (congrArg (fun k : ℕ => (k : ℕ∞)) (hd ⟨x, hx⟩)))
  · -- `LocalModel.isFaceStructured_toMPolyfold`
    intro M hne n W R hRM T hT hR
    exact B_model hB M hne ⟨R, hRM, hR.isTame hT⟩

#rt_check RoundTrip.V2_47.A_to_B [Polyfold.corollary_2_41, Polyfold.corollary_2_41_retract,
  Polyfold.LocalModel.isFaceStructured_toMPolyfold]
#rt_check RoundTrip.V2_47.B_to_A [Polyfold.corollary_2_41, Polyfold.corollary_2_41_retract,
  Polyfold.LocalModel.isFaceStructured_toMPolyfold]
#rt_overlap RoundTrip.V2_47.B_to_A [Polyfold.corollary_2_41, Polyfold.corollary_2_41_retract,
  Polyfold.LocalModel.isFaceStructured_toMPolyfold]

end RoundTrip.V2_47
