import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_130

set_option maxSynthPendingDepth 3

/-! Round trip for V17_130 (2021 Proposition 17.8.6 and (17.99), pp. 831–832: a proper covering
model restricts to a connected one over a `G`-invariant neighbourhood of `ō`; the component of `ō`
is `G`-invariant).

The item lists the definitions `restrictModel`, `restrictFunctor`, `restrictSource`,
`invariantComponent` (vocabulary) and four theorems; `A` is the conjunction of their types, at
universes `0, 0` (`B` takes `G`, `O`, `ObjE`, `MorE : Type`): **`proposition_17_8_6`** (the main
conjunct: for every open `U ∋ ō` an open `G`-invariant connected `O' ⊆ U` containing `ō`, and for
every choice of the paracompactness instances a proper covering model on the restriction with
distinguished point `ō`, connected), `exists_connected_restriction` ((17.99): the same for the
component `C = connectedComponent ō`, open and `G`-invariant), `restrictModel_connected`,
`isConnected_invariantComponent`.

* `A_to_B`: `B`'s first part is `proposition_17_8_6` without the model.  `B`'s second part
  ((17.99) for `⋂_g g⁻¹ U`) is the field `smul_mem'` of the vocabulary definition
  `invariantComponent` (a `SubMulAction` with carrier `connectedComponentIn (⋂_g g⁻¹ U) ō`); it is
  not taken from a conjunct of `A`.
* `B_to_A`: `proposition_17_8_6` from `B`'s first part and the vocabulary `restrictModel`
  (connected since `O'` is); `exists_connected_restriction` from `B`'s second part with `U = O`
  (the `SubMulAction` with carrier `connectedComponent ō`), openness from
  `MPolyfold.isOpen_connectedComponentIn`; `restrictModel_connected` and
  `isConnected_invariantComponent` re-proved outright (one-line project proofs:
  `isConnected_iff_connectedSpace`, `isConnected_connectedComponentIn_iff`, `mem_invariantCore`). -/

namespace RoundTrip.V17_130
open Polyfold Set

/-- The project's statement (universes `0, 0`). -/
def A : Prop :=
  (type_of% @Polyfold.proposition_17_8_6.{0, 0}) ∧
  (type_of% @Polyfold.exists_connected_restriction.{0, 0}) ∧
  (type_of% @Polyfold.ProperCoveringModel.restrictModel_connected.{0, 0}) ∧
  (type_of% @Polyfold.isConnected_invariantComponent.{0})

theorem A_holds : A :=
  ⟨@Polyfold.proposition_17_8_6.{0, 0}, @Polyfold.exists_connected_restriction.{0, 0},
    @Polyfold.ProperCoveringModel.restrictModel_connected.{0, 0},
    @Polyfold.isConnected_invariantComponent.{0}⟩

/-! ### The main conjunct -/

theorem main_A_to_B (h : type_of% @Polyfold.proposition_17_8_6.{0, 0}) : B := by
  intro G _ _ _ _ O _ _ _ _ P hP ObjE MorE _ _ _ _ _ _ E τ M
  refine ⟨fun U hU hpt => ?_, fun U _ hpt g x hx => ?_⟩
  · obtain ⟨O', hO', hpt', hsub, hconn, -⟩ := h M hU hpt
    exact ⟨O', hO', hpt', hsub, hconn⟩
  · exact (invariantComponent hP U M.pt M.smul_pt).smul_mem g hx

theorem main_B_to_A (hB : B) : type_of% @Polyfold.proposition_17_8_6.{0, 0} := by
  intro G _ _ _ _ O _ _ _ _ P hP ObjE MorE _ _ _ _ _ _ E τ M U hU hpt
  obtain ⟨O', hO', hpt', hsub, hconn⟩ := (hB G O P hP ObjE MorE E τ M).1 U hU hpt
  exact ⟨O', hO', hpt', hsub, hconn, fun {_ _} =>
    ⟨M.restrictModel O' hO' hpt', rfl, isConnected_iff_connectedSpace.1 hconn⟩⟩

/-! ### The other conjuncts -/

theorem exists_connected_restriction_of_B (hB : B) :
    type_of% @Polyfold.exists_connected_restriction.{0, 0} := by
  intro G _ _ _ _ O _ _ _ _ P hP ObjE MorE _ _ _ _ _ _ E τ M
  have hcore : (⋂ h : G, (fun y : O => h • y) ⁻¹' (univ : Set O)) = univ :=
    eq_univ_of_forall fun x => mem_iInter.2 fun _ => mem_univ _
  have hinv := (hB G O P hP ObjE MorE E τ M).2 univ isOpen_univ (mem_univ _)
  rw [hcore, connectedComponentIn_univ] at hinv
  let C : SubMulAction G O :=
    { carrier := connectedComponent M.pt
      smul_mem' := fun g x hx => hinv g x hx }
  have hC : IsOpen (C : Set O) := by
    have h := P.isOpen_connectedComponentIn isOpen_univ M.pt
    rwa [connectedComponentIn_univ] at h
  exact ⟨C, hC, mem_connectedComponent, rfl, fun {_ _} =>
    ⟨M.restrictModel C hC mem_connectedComponent, rfl,
      isConnected_iff_connectedSpace.1 isConnected_connectedComponent⟩⟩

theorem restrictModel_connected' :
    type_of% @Polyfold.ProperCoveringModel.restrictModel_connected.{0, 0} := by
  intros
  exact isConnected_iff_connectedSpace.1 ‹_›

theorem isConnected_invariantComponent' :
    type_of% @Polyfold.isConnected_invariantComponent.{0} := by
  intros
  apply isConnected_connectedComponentIn_iff.2
  apply mem_invariantCore <;> assumption

theorem A_to_B : A → B := fun h => main_A_to_B h.1

theorem B_to_A : B → A := fun hB =>
  ⟨main_B_to_A hB, exists_connected_restriction_of_B hB, restrictModel_connected',
    isConnected_invariantComponent'⟩

#rt_check RoundTrip.V17_130.main_A_to_B
  [Polyfold.proposition_17_8_6, Polyfold.exists_connected_restriction,
   Polyfold.ProperCoveringModel.restrictModel_connected, Polyfold.isConnected_invariantComponent]
#rt_check RoundTrip.V17_130.main_B_to_A
  [Polyfold.proposition_17_8_6, Polyfold.exists_connected_restriction,
   Polyfold.ProperCoveringModel.restrictModel_connected, Polyfold.isConnected_invariantComponent]
#rt_check RoundTrip.V17_130.A_to_B
  [Polyfold.proposition_17_8_6, Polyfold.exists_connected_restriction,
   Polyfold.ProperCoveringModel.restrictModel_connected, Polyfold.isConnected_invariantComponent]
#rt_check RoundTrip.V17_130.B_to_A
  [Polyfold.proposition_17_8_6, Polyfold.exists_connected_restriction,
   Polyfold.ProperCoveringModel.restrictModel_connected, Polyfold.isConnected_invariantComponent]
#rt_overlap RoundTrip.V17_130.B_to_A
  [Polyfold.proposition_17_8_6, Polyfold.exists_connected_restriction,
   Polyfold.ProperCoveringModel.restrictModel_connected, Polyfold.isConnected_invariantComponent]

end RoundTrip.V17_130
