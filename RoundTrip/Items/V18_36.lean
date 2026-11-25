import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V18_36

/-! Round trip for V18_36 (2021 Theorem 18.3.5, p. 853; 2017: Theorem 18.5): sums and products
of structurable sc⁺-multisection functors.

The item lists `theorem_18_3_5` and the example `ReflectionBundle.theorem_18_3_5_witness`;
`A` is the conjunction of their types, with `theorem_18_3_5` at universe `0` (`B` lives in
`GCT.{0}`).

* `A_to_B`: `B`'s two conjuncts are `theorem_18_3_5` with `β` resp. `Λ₂` specialized
  (for the `⊙` part take `Λ₂ := Λ₁`).
* `B_to_A`: `theorem_18_3_5` is the conjunction of `B`'s two clauses.  The witness: the
  non-trivial structurable `Λ` comes from `proposition_18_4_3_witness` (not an item theorem),
  `β = 2` is sc-smooth (`isScSmoothMap_real_const`), and `Λ ⊕ Λ`, `2 ⊙ Λ` are structurable by
  `B` on the reflection bundle. -/

namespace RoundTrip.V18_36
open Polyfold
open Polyfold.GCT.VectorBundle Polyfold.GCT.VectorBundle.ReflectionBundle

/-- The project's statement (`theorem_18_3_5` at universe `0`, and its example). -/
def A : Prop :=
  (type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_3_5.{0}) ∧
  (type_of% @Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_3_5_witness)

theorem A_holds : A :=
  ⟨@Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_3_5.{0},
    @Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_3_5_witness⟩

/-- `B` and the main conjunct `theorem_18_3_5` say the same thing. -/
theorem main_to_B :
    (type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_3_5.{0}) →
      B := by
  intro h C S V Q
  exact ⟨fun Λ₁ Λ₂ h₁ h₂ => (h Q h₁ h₂ (β := fun _ => 0) ⟨fun _ => rfl,
      fun _ => isScSmoothMap_real_const 0⟩).1,
    fun β Λ₁ hβ h₁ => (h Q h₁ h₁ hβ).2⟩

theorem B_to_main : B →
    (type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_3_5.{0}) := by
  intro hB C V S Q Λ₁ Λ₂ h₁ h₂ β hβ
  exact ⟨(hB C S V Q).1 Λ₁ Λ₂ h₁ h₂, (hB C S V Q).2 β Λ₁ hβ h₁⟩

theorem A_to_B : A → B := fun h => main_to_B h.1

theorem B_to_A : B → A := by
  intro hB
  refine ⟨B_to_main hB, ?_⟩
  obtain ⟨-, -, Λ, -, hst, -, -, hpos⟩ := proposition_18_4_3_witness
  have hβ : Polyfold.GCT.PolyfoldConstruction.reflectionConstruction.IsScSmoothFunctionFunctor
      (fun _ => (2 : ℝ)) := ⟨fun _ => rfl, fun _ => isScSmoothMap_real_const 2⟩
  exact ⟨Λ, hst, hpos, hβ, (hB _ _ _ reflQ).1 Λ Λ hst hst, (hB _ _ _ reflQ).2 _ Λ hβ hst⟩

#rt_check RoundTrip.V18_36.A_to_B
  [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_3_5,
   Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_3_5_witness]
#rt_check RoundTrip.V18_36.B_to_A
  [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_3_5,
   Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_3_5_witness]
#rt_check RoundTrip.V18_36.main_to_B
  [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_3_5,
   Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_3_5_witness]
#rt_check RoundTrip.V18_36.B_to_main
  [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_3_5,
   Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_3_5_witness]
#rt_overlap RoundTrip.V18_36.B_to_A
  [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_3_5,
   Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_3_5_witness]

end RoundTrip.V18_36
