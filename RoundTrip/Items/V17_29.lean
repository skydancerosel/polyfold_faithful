import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_29

set_option maxSynthPendingDepth 3

/-! Round trip for V17_29 (2021 Theorem 17.1.26, p. 759: the class `c_C` of polyfold structures on
`|C|` under (ZHOU)).

`A` is the conjunction of the types of `modelPolyfoldStructure_equiv`, `polyfoldClass_eq`,
`theorem_17_1_26` and `z3Taut_polyfoldClass` (the definition `polyfoldClass` is vocabulary),
with the universe `u := 0`.

* `A_to_B`: `cl := S.polyfoldClass h`; for every covering family, `theorem_17_1_26` gives
  `[(X_Ψ, |Γ_Ψ|)] = c_C`; `B`'s structure is `modelPolyfoldStructure c hZ` up to proofs.
* `B_to_A`: from `B`'s class `cl`, both `[(X_Ψ, |Γ_Ψ|)]` and `[(X_Ψ', |Γ_Ψ'|)]` are `cl`, so the
  structures are equivalent (`Quotient.exact`); `polyfoldClass h` is the class of the covering family
  `h.choose`, hence `cl` too.  The ℤ/3 witness is the instance of `polyfoldClass_eq` thus obtained.
-/

namespace RoundTrip.V17_29
open Polyfold

def A : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.modelPolyfoldStructure_equiv.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.polyfoldClass_eq.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.theorem_17_1_26.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.z3Taut_polyfoldClass)

theorem A_holds : A :=
  ⟨@Polyfold.GCT.PolyfoldConstruction.modelPolyfoldStructure_equiv.{0},
    @Polyfold.GCT.PolyfoldConstruction.polyfoldClass_eq.{0},
    @Polyfold.GCT.PolyfoldConstruction.theorem_17_1_26.{0},
    @Polyfold.GCT.PolyfoldConstruction.z3Taut_polyfoldClass⟩

/-- `B`'s polyfold structure is the project's `modelPolyfoldStructure` (up to proofs). -/
theorem mk_eq {C : GCT.{0}} (S : C.PolyfoldConstruction) (c : S.CoveringFamily)
    (hp : (S.modelEP c.Ψ).X.HasParacompactOrbitSpace) (hz : (S.modelEP c.Ψ).X.IsZhou)
    (hh : IsHomeomorph (S.modelFunctor c.Ψ).orbitMap) :
    PolyfoldStructure.mk (S.modelEP c.Ψ) hp hz (hh.homeomorph _) =
      S.modelPolyfoldStructure c hz := rfl

theorem main_A_to_B : (type_of% @Polyfold.GCT.PolyfoldConstruction.theorem_17_1_26.{0}) → B := by
  intro h26 C S hZ
  refine ⟨S.polyfoldClass hZ, fun c => ?_⟩
  obtain ⟨-, hc⟩ := h26 S hZ
  obtain ⟨hZc, -, -, hcl⟩ := hc c
  exact ⟨S.hasParacompactOrbitSpace_model c, hZc, (S.lemma_17_1_15 c).2, hcl⟩

theorem A_to_B : A → B := fun h => main_A_to_B h.2.2.1

/-- From `B`: every covering family represents `B`'s class. -/
theorem class_eq_of_B (hB : B) {C : GCT.{0}} (S : C.PolyfoldConstruction) (h : S.IsZhou) :
    ∃ cl : PolyfoldClass C.toGroupoidStr.OrbitSpace, ∀ (c : S.CoveringFamily)
      (hz : (S.modelEP c.Ψ).X.IsZhou),
      (⟦S.modelPolyfoldStructure c hz⟧ : PolyfoldClass C.toGroupoidStr.OrbitSpace) = cl := by
  obtain ⟨cl, hcl⟩ := hB C S h
  refine ⟨cl, fun c hz => ?_⟩
  obtain ⟨hp, hz', hh, e⟩ := hcl c
  exact e

theorem polyfoldClass_eq_of_B (hB : B) {C : GCT.{0}} (S : C.PolyfoldConstruction) (h : S.IsZhou)
    (c : S.CoveringFamily) (hz : (S.modelEP c.Ψ).X.IsZhou) :
    (⟦S.modelPolyfoldStructure c hz⟧ : PolyfoldClass C.toGroupoidStr.OrbitSpace) =
      S.polyfoldClass h := by
  obtain ⟨cl, hcl⟩ := class_eq_of_B hB S h
  exact (hcl c hz).trans (hcl h.choose h.choose_spec).symm

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro C S c c' hZ hZ'
    have h : S.IsZhou := ⟨c, hZ⟩
    obtain ⟨cl, hcl⟩ := class_eq_of_B hB S h
    exact Quotient.exact ((hcl c hZ).trans (hcl c' hZ').symm)
  · intro C S h c
    exact polyfoldClass_eq_of_B hB S h c (h.model c)
  · intro C S h
    exact ⟨inferInstance, fun c => ⟨h.model c, rfl, rfl, polyfoldClass_eq_of_B hB S h c _⟩⟩
  · exact ⟨_, polyfoldClass_eq_of_B hB _ GCT.PolyfoldConstruction.z3Taut_properties.1 _
      (GCT.PolyfoldConstruction.z3Taut_properties.1.model _)⟩


/-! ### The main conjunct `theorem_17_1_26` alone -/


theorem main_B_to_A : B → (type_of% @Polyfold.GCT.PolyfoldConstruction.theorem_17_1_26.{0}) :=
  fun hB => (B_to_A hB).2.2.1

#rt_check RoundTrip.V17_29.A_to_B [Polyfold.GCT.PolyfoldConstruction.modelPolyfoldStructure_equiv,
  Polyfold.GCT.PolyfoldConstruction.polyfoldClass_eq,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_26,
  Polyfold.GCT.PolyfoldConstruction.z3Taut_polyfoldClass]
#rt_check RoundTrip.V17_29.B_to_A [Polyfold.GCT.PolyfoldConstruction.modelPolyfoldStructure_equiv,
  Polyfold.GCT.PolyfoldConstruction.polyfoldClass_eq,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_26,
  Polyfold.GCT.PolyfoldConstruction.z3Taut_polyfoldClass]
#rt_overlap RoundTrip.V17_29.B_to_A [Polyfold.GCT.PolyfoldConstruction.modelPolyfoldStructure_equiv,
  Polyfold.GCT.PolyfoldConstruction.polyfoldClass_eq,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_26,
  Polyfold.GCT.PolyfoldConstruction.z3Taut_polyfoldClass]

#rt_check RoundTrip.V17_29.main_A_to_B [Polyfold.GCT.PolyfoldConstruction.modelPolyfoldStructure_equiv,
  Polyfold.GCT.PolyfoldConstruction.polyfoldClass_eq,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_26,
  Polyfold.GCT.PolyfoldConstruction.z3Taut_polyfoldClass]
#rt_check RoundTrip.V17_29.main_B_to_A [Polyfold.GCT.PolyfoldConstruction.modelPolyfoldStructure_equiv,
  Polyfold.GCT.PolyfoldConstruction.polyfoldClass_eq,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_26,
  Polyfold.GCT.PolyfoldConstruction.z3Taut_polyfoldClass]

end RoundTrip.V17_29
