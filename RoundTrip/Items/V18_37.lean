import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V18_37

/-! Round trip for V18_37 (2021 Theorem 18.3.6, p. 853; 2017: Theorem 18.6): the pull-back of a
structurable sc⁺-multisection functor by an sc-smooth strong bundle proper covering functor.

The item lists the definitions `StrongBundleProperCovering`, `ReflectionBundle.reflIdCovering`
(vocabulary) and the theorems `theorem_18_3_6`, `ReflectionBundle.theorem_18_3_6_witness`; `A`
is the conjunction of the two theorems' types, `theorem_18_3_6` at universe `0`.  `B` uses the
project's `StrongBundleProperCovering` as its notion of covering functor, so the two main
statements coincide up to argument order (`Λ ∘ P̃.obj` is `fun e => Λ (P̃.obj e)`
definitionally).

* `A_to_B`: `theorem_18_3_6`.
* `B_to_A`: `theorem_18_3_6` from `B`; the witness from the non-trivial structurable `Λ` of
  `proposition_18_4_3_witness` (not an item theorem) and `B` applied to `reflIdCovering`. -/

namespace RoundTrip.V18_37
open Polyfold
open Polyfold.GCT.VectorBundle Polyfold.GCT.VectorBundle.ReflectionBundle

/-- The project's statement (`theorem_18_3_6` at universe `0`, and its example). -/
def A : Prop :=
  (type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_3_6.{0}) ∧
  (type_of% @Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_3_6_witness)

theorem A_holds : A :=
  ⟨@Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_3_6.{0},
    @Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_3_6_witness⟩

theorem main_to_B :
    (type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_3_6.{0}) →
      B := by
  intro h C C' S S' V V' Q Q' Pt Λ hΛ
  exact h Pt hΛ

theorem B_to_main : B →
    (type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_3_6.{0}) := by
  intro hB C V S Q C' V' S' Q' P Λ hΛ
  exact hB C C' S S' V V' Q Q' P Λ hΛ

theorem A_to_B : A → B := fun h => main_to_B h.1

theorem B_to_A : B → A := by
  intro hB
  refine ⟨B_to_main hB, ?_⟩
  obtain ⟨-, -, Λ, -, hst, -, -, hpos⟩ := proposition_18_4_3_witness
  exact ⟨Λ, hst, hpos, hB _ _ _ _ _ _ reflQ reflQ reflIdCovering Λ hst⟩

#rt_check RoundTrip.V18_37.A_to_B
  [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_3_6,
   Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_3_6_witness]
#rt_check RoundTrip.V18_37.B_to_A
  [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_3_6,
   Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_3_6_witness]
#rt_check RoundTrip.V18_37.main_to_B
  [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_3_6,
   Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_3_6_witness]
#rt_check RoundTrip.V18_37.B_to_main
  [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_3_6,
   Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_3_6_witness]
#rt_overlap RoundTrip.V18_37.B_to_A
  [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_3_6,
   Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_3_6_witness]

end RoundTrip.V18_37
