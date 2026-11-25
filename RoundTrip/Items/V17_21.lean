import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_21

set_option maxSynthPendingDepth 3

/-! Round trip for V17_21 (2021 Theorem 17.1.18, p. 756: the canonical generalized isomorphisms
`f_{Ψ,Ψ'}`).

The item lists the definition `comparison` (vocabulary, `f_{Ψ,Ψ'}`) and eight theorems; `A` is the
conjunction of their types, at universe `0` (`B` is stated for `GCT.{0}`; the two examples have no
universe parameter).  The conjuncts: `isGeneralizedIso_comparison`, `comparison_self`,
`comparison_comp`, `orbitMap_comparison`, `isHomeomorph_orbitMap_comparison`, `theorem_17_1_18`
(their conjunction), and the examples `reflection_comparison`, `overlap_comparison`.

* `A_to_B`: the first five claims of `B` are `theorem_17_1_18`.  `B`'s sixth claim, `|Γ_Ψ|` is a
  homeomorphism ("`(X_Ψ, |Γ_Ψ|)` is a weak polyfold structure"), is not among `A`'s conjuncts; it
  comes from the non-item `modelOrbitHomeomorph` (Lemma 17.1.15, `|Γ_Ψ|` a homeomorphism).
* `B_to_A`: the general conjuncts are `B`; the examples are `B` specialised to the reflection and
  overlap constructions, except the last clause of `reflection_comparison` (an object `p` of the
  weak fibred product whose canonical morphism is `(−1, 0) ≠ 1`), which `B` does not mention;
  it is re-proved outright (the project's proof, from `fibredProductObjEquiv`). -/

namespace RoundTrip.V17_21
open Polyfold Polyfold.EPLocalization Polyfold.GCT.PolyfoldConstruction CategoryTheory

def A : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.isGeneralizedIso_comparison.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.comparison_self.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.comparison_comp.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.orbitMap_comparison.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.isHomeomorph_orbitMap_comparison.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.theorem_17_1_18.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.reflection_comparison) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.overlap_comparison)

theorem A_holds : A :=
  ⟨@Polyfold.GCT.PolyfoldConstruction.isGeneralizedIso_comparison.{0},
    @Polyfold.GCT.PolyfoldConstruction.comparison_self.{0},
    @Polyfold.GCT.PolyfoldConstruction.comparison_comp.{0},
    @Polyfold.GCT.PolyfoldConstruction.orbitMap_comparison.{0},
    @Polyfold.GCT.PolyfoldConstruction.isHomeomorph_orbitMap_comparison.{0},
    @Polyfold.GCT.PolyfoldConstruction.theorem_17_1_18.{0},
    @Polyfold.GCT.PolyfoldConstruction.reflection_comparison,
    @Polyfold.GCT.PolyfoldConstruction.overlap_comparison⟩

theorem A_to_B : A → B := by
  rintro ⟨-, -, -, -, -, h, -, -⟩ C S c c' c''
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h S c c' c''
  exact ⟨h₁, h₂, h₃, h₄, h₅, (S.modelOrbitHomeomorph c).isHomeomorph⟩

theorem B_to_A : B → A := by
  intro hB
  have h18 : type_of% @Polyfold.GCT.PolyfoldConstruction.theorem_17_1_18.{0} :=
    fun {C} S c c' c'' => let h := hB C S c c' c''; ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
  refine ⟨fun {C} S c c' => (h18 S c c' c').1, fun {C} S c => (h18 S c c c).2.1,
    fun {C} S c c' c'' => (h18 S c c' c'').2.2.1, fun {C} S c c' => (h18 S c c' c').2.2.2.1,
    fun {C} S c c' => (h18 S c c' c').2.2.2.2, h18, ?_, ?_⟩
  · obtain ⟨h₁, -, -, h₄, h₅⟩ := h18 reflectionConstruction reflectionSingleFamily
      reflectionPairFamily reflectionPairFamily
    refine ⟨h₁, h₄, h₅, (reflectionConstruction.fibredProductObjEquiv _ _ _).symm
      ⟨((), true), ⟨(0 : Fin 1 → ℝ), ((-1 : ℤˣ), 0), (0 : Fin 1 → ℝ), rfl, smul_zero _⟩⟩, rfl,
      fun h => absurd (congrArg Prod.fst h) (by decide)⟩
  · obtain ⟨h₁, -, -, h₄, h₅⟩ := h18 overlapConstruction overlapSingleFamily
      overlapCoveringFamily overlapCoveringFamily
    exact ⟨h₁, h₄, h₅⟩

/-- The main conjunct `theorem_17_1_18` alone. -/
theorem main_to_B : type_of% @Polyfold.GCT.PolyfoldConstruction.theorem_17_1_18.{0} → B := by
  intro h C S c c' c''
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h S c c' c''
  exact ⟨h₁, h₂, h₃, h₄, h₅, (S.modelOrbitHomeomorph c).isHomeomorph⟩

theorem B_to_main : B → type_of% @Polyfold.GCT.PolyfoldConstruction.theorem_17_1_18.{0} :=
  fun hB {C} S c c' c'' => let h := hB C S c c' c''
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

#rt_check RoundTrip.V17_21.A_to_B [Polyfold.GCT.PolyfoldConstruction.isGeneralizedIso_comparison,
  Polyfold.GCT.PolyfoldConstruction.comparison_self, Polyfold.GCT.PolyfoldConstruction.comparison_comp,
  Polyfold.GCT.PolyfoldConstruction.orbitMap_comparison,
  Polyfold.GCT.PolyfoldConstruction.isHomeomorph_orbitMap_comparison,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_18,
  Polyfold.GCT.PolyfoldConstruction.reflection_comparison,
  Polyfold.GCT.PolyfoldConstruction.overlap_comparison]
#rt_check RoundTrip.V17_21.B_to_A [Polyfold.GCT.PolyfoldConstruction.isGeneralizedIso_comparison,
  Polyfold.GCT.PolyfoldConstruction.comparison_self, Polyfold.GCT.PolyfoldConstruction.comparison_comp,
  Polyfold.GCT.PolyfoldConstruction.orbitMap_comparison,
  Polyfold.GCT.PolyfoldConstruction.isHomeomorph_orbitMap_comparison,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_18,
  Polyfold.GCT.PolyfoldConstruction.reflection_comparison,
  Polyfold.GCT.PolyfoldConstruction.overlap_comparison]
#rt_check RoundTrip.V17_21.main_to_B [Polyfold.GCT.PolyfoldConstruction.isGeneralizedIso_comparison,
  Polyfold.GCT.PolyfoldConstruction.comparison_self, Polyfold.GCT.PolyfoldConstruction.comparison_comp,
  Polyfold.GCT.PolyfoldConstruction.orbitMap_comparison,
  Polyfold.GCT.PolyfoldConstruction.isHomeomorph_orbitMap_comparison,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_18,
  Polyfold.GCT.PolyfoldConstruction.reflection_comparison,
  Polyfold.GCT.PolyfoldConstruction.overlap_comparison]
#rt_check RoundTrip.V17_21.B_to_main [Polyfold.GCT.PolyfoldConstruction.isGeneralizedIso_comparison,
  Polyfold.GCT.PolyfoldConstruction.comparison_self, Polyfold.GCT.PolyfoldConstruction.comparison_comp,
  Polyfold.GCT.PolyfoldConstruction.orbitMap_comparison,
  Polyfold.GCT.PolyfoldConstruction.isHomeomorph_orbitMap_comparison,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_18,
  Polyfold.GCT.PolyfoldConstruction.reflection_comparison,
  Polyfold.GCT.PolyfoldConstruction.overlap_comparison]
#rt_overlap RoundTrip.V17_21.B_to_A [Polyfold.GCT.PolyfoldConstruction.isGeneralizedIso_comparison,
  Polyfold.GCT.PolyfoldConstruction.comparison_self, Polyfold.GCT.PolyfoldConstruction.comparison_comp,
  Polyfold.GCT.PolyfoldConstruction.orbitMap_comparison,
  Polyfold.GCT.PolyfoldConstruction.isHomeomorph_orbitMap_comparison,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_18,
  Polyfold.GCT.PolyfoldConstruction.reflection_comparison,
  Polyfold.GCT.PolyfoldConstruction.overlap_comparison]

end RoundTrip.V17_21
