import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V18_40

/-! Round trip for V18_40 (2021, the construction on p. 854 and Proposition 18.4.3, p. 855;
2017: Proposition 18.1).

The item lists `exists_atomicData`, `proposition_18_4_3`, `proposition_18_4_3_formula` (the
construction in a covering model), the example `ReflectionBundle.proposition_18_4_3_witness`, and
the construction of p. 854 in one strong bundle uniformizer (`Chapter18/MultisectionConstructionText`):
`textLam_indep`, `proposition_18_4_3_text`, `TextData.textLam_eq`, `proposition_18_4_3_text_exists`
and `proposition_18_4_3_cutoff`.  `A` is the conjunction of their types, at universe `0`.

The main conjunct is `proposition_18_4_3_cutoff`: the text's `Λ` for `s₁ = β·s`, a local
sc⁺-section `s` near `q₀` and an sc-smooth bump `β : O → [0, 1]`, `β(q₀) = 1`, supported in a
small `W ∋ q₀`, with `Λ` written through the morphisms `φ : Ψ(q) → P(e)`.  Its functions
`cutoffValue`, `CutoffLift`, `cutoffLam` have the same bodies as `B`'s `phiValue`, `IsLift`, `lam`,
so `B` and the main conjunct are the same statement (both directions by unfolding).  `B` says
nothing about the other conjuncts (the construction in a covering model, the identification
`textLam_eq` with it, the satisfiability `proposition_18_4_3_text_exists`, the example), so
`B → A` is not claimed. -/

namespace RoundTrip.V18_40
open Polyfold

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.exists_atomicData.{0}) ∧
  (type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_4_3.{0}) ∧
  (type_of%
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_4_3_formula.{0}) ∧
  (type_of% @Polyfold.GCT.VectorBundle.ReflectionBundle.proposition_18_4_3_witness) ∧
  (type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.textLam_indep.{0}) ∧
  (type_of%
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_4_3_text.{0}) ∧
  (type_of%
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.TextData.textLam_eq.{0}) ∧
  (type_of%
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_4_3_text_exists.{0}) ∧
  (type_of%
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_4_3_cutoff.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.exists_atomicData.{0},
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_4_3.{0},
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_4_3_formula.{0},
    @Polyfold.GCT.VectorBundle.ReflectionBundle.proposition_18_4_3_witness,
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.textLam_indep.{0},
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_4_3_text.{0},
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.TextData.textLam_eq.{0},
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_4_3_text_exists.{0},
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_4_3_cutoff.{0}⟩

/-- The main conjunct: Proposition 18.4.3 for the text's `Λ` with `s₁ = β·s`. -/
def Amain : Prop :=
  type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_4_3_cutoff.{0}

theorem main_to_B : Amain → B := by
  intro h C S V Q hF hb α Ψb hΨb q₀ hq₀ s hs Vs hVs hq₀Vs hsV
  exact h (Q := Q) hF hb α Ψb hΨb q₀ hq₀ s hs Vs hVs hq₀Vs hsV

theorem B_to_main : B → Amain := by
  intro h C V S Q hF hb α Ψb hΨb q₀ hq₀ s hs Vs hVs hq₀Vs hsV
  exact h C S V Q hF hb α Ψb hΨb q₀ hq₀ s hs Vs hVs hq₀Vs hsV

theorem A_to_B : A → B := fun h => main_to_B h.2.2.2.2.2.2.2.2

#rt_check RoundTrip.V18_40.A_to_B
  [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.exists_atomicData,
   Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_4_3,
   Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_4_3_formula,
   Polyfold.GCT.VectorBundle.ReflectionBundle.proposition_18_4_3_witness,
   Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.textLam_indep,
   Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_4_3_text,
   Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.TextData.textLam_eq,
   Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_4_3_text_exists,
   Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_4_3_cutoff]
#rt_check RoundTrip.V18_40.main_to_B
  [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_4_3_text,
   Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_4_3_cutoff]
#rt_check RoundTrip.V18_40.B_to_main
  [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_4_3_text,
   Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_4_3_cutoff]

end RoundTrip.V18_40
