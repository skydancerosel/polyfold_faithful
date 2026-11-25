import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_102

set_option maxSynthPendingDepth 3

namespace RoundTrip.V17_102
open Polyfold CategoryTheory
open Polyfold.GCT.PolyfoldConstruction

/-- The project's statement, universe `0`. -/
def A : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_5_7.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.modelGrPush_tangentValue_eq.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GCT.PolyfoldConstruction.proposition_17_5_7.{0},
    @Polyfold.GCT.PolyfoldConstruction.modelGrPush_tangentValue_eq.{0}⟩

/-- The main conjunct. -/
def Main : Prop := type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_5_7.{0}

/-- `Main ⇒ B`: the section functor built from `(1)` (values in `Gr`) and `(3)` (naturality);
its values are `TΓ_Ψ*(TΓ_Ψ^*Θ)` for every covering family by `(2)`, applied at the point and
morphism chosen in the definition of `tangentSectionVia`. -/
theorem main_to_B : Main → B := by
  intro h C S hU Θ hΘ
  have H := h (S := S) hU hΘ
  let F : S.regSubInf.Ob ⥤ (S.grFunctorC hU).Elements :=
    { obj := fun α => ⟨α, ⟨S.branchedTangentSection hU Θ (smoothObjVal α),
        H.1 _ (tangentObj_smoothObjVal hU α)⟩⟩
      map := fun {α β} f => ⟨f, by
        apply Subtype.ext
        change S.grPushC (smoothMorVal f) (S.branchedTangentSection hU Θ (smoothObjVal α)) =
          S.branchedTangentSection hU Θ (smoothObjVal β)
        have h3 := H.2.2.1 (smoothMorVal f)
          (by rw [tgt_smoothMorVal]; exact tangentObj_smoothObjVal hU β)
        rw [src_smoothMorVal, tgt_smoothMorVal] at h3
        exact h3.symm⟩
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  refine ⟨F, rfl, fun α c => ?_⟩
  change S.branchedTangentSection hU Θ (smoothObjVal α) =
    S.tangentSectionVia hU c.Ψ Θ (smoothObjVal α)
  have hex : ∃ x : S.ModelObj c.Ψ, ∃ φ : C.Mor,
      C.toGroupoidStr.src φ = (S.modelFunctor c.Ψ).obj x ∧
        C.toGroupoidStr.tgt φ = smoothObjVal α :=
    (GroupoidFunctor.essSurj_iff _).1 (S.modelFunctor_essSurj c.isCoveringFamily) _
  rw [tangentSectionVia, dif_pos hex]
  exact H.2.1 c _ (tangentObj_smoothObjVal hU α) _ _ hex.choose_spec.choose_spec.1
    hex.choose_spec.choose_spec.2

theorem A_to_B : A → B := fun h => main_to_B h.1

#rt_check RoundTrip.V17_102.A_to_B [Polyfold.GCT.PolyfoldConstruction.proposition_17_5_7, Polyfold.GCT.PolyfoldConstruction.modelGrPush_tangentValue_eq]
#rt_check RoundTrip.V17_102.main_to_B [Polyfold.GCT.PolyfoldConstruction.proposition_17_5_7, Polyfold.GCT.PolyfoldConstruction.modelGrPush_tangentValue_eq]

#rt_overlap RoundTrip.V17_102.A_to_B [Polyfold.GCT.PolyfoldConstruction.proposition_17_5_7, Polyfold.GCT.PolyfoldConstruction.modelGrPush_tangentValue_eq]

/-! `B ⇒ A` is not proved.  `B` speaks only about objects of `C_∞` (`S.regSubInf`), and on them
only about the value `tangentSectionVia` computed at the point `x` and morphism `φ : Γ(x) → α`
chosen in its definition.  `A` states (1)–(4) of `proposition_17_5_7` for every `α ∈ C¹`
(`TangentObj α`: regularity `≥ 1` and `F(α) ≠ ∅`) and (17.86) for every `x` and every
`φ : Γ(x) → α` (`modelGrPush_tangentValue_eq` and part (2)); neither follows from `B`. -/

end RoundTrip.V17_102
