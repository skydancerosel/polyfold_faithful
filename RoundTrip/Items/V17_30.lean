import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_30

set_option maxSynthPendingDepth 3

/-! Round trip for V17_30 (2021 Theorem 17.1.27, pp. 759–761, (17.17)–(17.19): the canonical
natural transformation `τ : Γ ∘ π₁ → Γ' ∘ π₂`).

`A` is the conjunction of the types of `canonicalNatTrans_app`, `isEquivalence_modelFunctorLeft`
and `theorem_17_1_27` (the definitions `modelFunctorLeft/Right`, `canonicalNatTrans`,
`fibredProductObjEquiv` are vocabulary), with `u := 0`.

* `A_to_B`: the equivalences and `τ` from `theorem_17_1_27`; `τ.app o` has value `φ''`, so it is
  `homMk φ''` (`Subtype.ext`).
* `B_to_A`: `theorem_17_1_27` from `B` (`τ` is `B`'s, an isomorphism since `C` is a groupoid);
  `isEquivalence_modelFunctorLeft` for arbitrary covering index families from `B` applied to the
  covering families `⟨ι, Ψ, hΨ⟩`, `⟨ι', Ψ', hΨ'⟩`; `canonicalNatTrans_app` is `rfl` (a definitional
  fact about the vocabulary definition, proved without `B`).
-/

namespace RoundTrip.V17_30
open Polyfold CategoryTheory

def A : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.canonicalNatTrans_app.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.isEquivalence_modelFunctorLeft.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.theorem_17_1_27.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GCT.PolyfoldConstruction.canonicalNatTrans_app.{0},
    @Polyfold.GCT.PolyfoldConstruction.isEquivalence_modelFunctorLeft.{0},
    @Polyfold.GCT.PolyfoldConstruction.theorem_17_1_27.{0}⟩

theorem main_A_to_B : (type_of% @Polyfold.GCT.PolyfoldConstruction.theorem_17_1_27.{0}) → B := by
  intro h C S c c'
  obtain ⟨e1, e2, τ, -, hτ⟩ := h S c c'
  refine ⟨e1, e2, τ, fun o => ?_⟩
  have h1 := (τ.app o).2.1
  have h2 := (τ.app o).2.2
  rw [hτ o] at h1 h2
  exact ⟨h1, h2, Subtype.ext (hτ o)⟩

theorem A_to_B : A → B := fun h => main_A_to_B h.2.2

theorem main_B_to_A : B → (type_of% @Polyfold.GCT.PolyfoldConstruction.theorem_17_1_27.{0}) := by
  intro hB C S c c'
  obtain ⟨e1, e2, τ, hτ⟩ := hB C S c c'
  refine ⟨e1, e2, τ, NatIso.isIso_of_isIso_app _, fun p => ?_⟩
  obtain ⟨h1, h2, e⟩ := hτ p
  rw [e]
  rfl

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun _ _ _ _ _ _ _ => rfl, ?_, main_B_to_A hB⟩
  intro C S ι ι' Ψ Ψ' hΨ' hΨ
  exact (hB C S ⟨ι, Ψ, hΨ⟩ ⟨ι', Ψ', hΨ'⟩).1

#rt_check RoundTrip.V17_30.A_to_B [Polyfold.GCT.PolyfoldConstruction.canonicalNatTrans_app,
  Polyfold.GCT.PolyfoldConstruction.isEquivalence_modelFunctorLeft,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_27]
#rt_check RoundTrip.V17_30.B_to_A [Polyfold.GCT.PolyfoldConstruction.canonicalNatTrans_app,
  Polyfold.GCT.PolyfoldConstruction.isEquivalence_modelFunctorLeft,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_27]
#rt_overlap RoundTrip.V17_30.B_to_A [Polyfold.GCT.PolyfoldConstruction.canonicalNatTrans_app,
  Polyfold.GCT.PolyfoldConstruction.isEquivalence_modelFunctorLeft,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_27]
#rt_check RoundTrip.V17_30.main_A_to_B [Polyfold.GCT.PolyfoldConstruction.canonicalNatTrans_app,
  Polyfold.GCT.PolyfoldConstruction.isEquivalence_modelFunctorLeft,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_27]
#rt_check RoundTrip.V17_30.main_B_to_A [Polyfold.GCT.PolyfoldConstruction.canonicalNatTrans_app,
  Polyfold.GCT.PolyfoldConstruction.isEquivalence_modelFunctorLeft,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_27]

end RoundTrip.V17_30
