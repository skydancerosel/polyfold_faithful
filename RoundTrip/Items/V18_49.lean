import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V18_49

/-! Round trip for V18_49 (2021 Proposition 18.5.6, p. 859; 2017: Proposition 18.2):
orientations of `f` and of its covering models.

The item lists `proposition_18_5_6_one_hyp`, `_two_hyp`, `_three_hyp` and the example
`ReflectionBundle.reflDiag_orientation_hyp`; `A` is the conjunction of their types, the first
three at universe `0`.  `B` uses the project's vocabulary for orientations and the same extra
hypotheses (`hF`, `hT`, `hbump`, `hfT`), so:

* (1) is the same statement.
* (2): `A` states the pull-backs to two covering families `c`, `c'`; `B` to one, for all `c`.
* (3): `A` reads "correspond under the comparison" as `modelTransport c' c o' = o`, `B` as
  `modelTransport c c' m = m'`.  The left-hand sides agree up to the order of the conjuncts
  `pullCat c O = m ∧ pullCat c' O = m'`, so each form is the other with `(c, m)` and `(c', m')`
  exchanged; the two readings are equivalent.
* The example `reflDiag_orientation_hyp` (closed, about the reflection bundle) is not a
  consequence of `B`; in `B_to_A` it is re-proved from the same non-item lemmas as in the
  project. -/

namespace RoundTrip.V18_49
open Polyfold
open Polyfold.GCT.VectorBundle Polyfold.GCT.VectorBundle.ReflectionBundle
open Polyfold.GCT.PolyfoldConstruction

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of%
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_5_6_one_hyp.{0}) ∧
  (type_of%
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_5_6_two_hyp.{0}) ∧
  (type_of%
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_5_6_three_hyp.{0}) ∧
  (type_of% @Polyfold.GCT.VectorBundle.ReflectionBundle.reflDiag_orientation_hyp)

theorem A_holds : A :=
  ⟨@Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_5_6_one_hyp.{0},
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_5_6_two_hyp.{0},
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_5_6_three_hyp.{0},
    @Polyfold.GCT.VectorBundle.ReflectionBundle.reflDiag_orientation_hyp⟩

/-- The three clauses of Proposition 18.5.6 in the project's form (the main content). -/
def Amain : Prop :=
  (type_of%
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_5_6_one_hyp.{0}) ∧
  (type_of%
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_5_6_two_hyp.{0}) ∧
  (type_of%
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_5_6_three_hyp.{0})

theorem main_to_B : Amain → B := by
  rintro ⟨h1, h2, h3⟩ C S V Q hF hT hb f hf hfT
  refine ⟨fun c => h1 Q hf hb hT hfT hF c, fun o ho c => (h2 Q hf hb hT hfT hF ho c c).1,
    fun c c' m m' hm hm' => ?_⟩
  rw [← h3 Q hf hb hT hfT hF c' c hm' hm]
  exact ⟨fun ⟨O, hO, e1, e2⟩ => ⟨O, hO, e2, e1⟩, fun ⟨O, hO, e1, e2⟩ => ⟨O, hO, e2, e1⟩⟩

theorem B_to_main : B → Amain := by
  intro hB
  refine ⟨?_, ?_, ?_⟩
  · intro C V S Q f hf hb hT hfT hF c
    exact (hB C S V Q hF hT hb f hf hfT).1 c
  · intro C V S Q f hf hb hT hfT hF o ho c c'
    exact ⟨(hB C S V Q hF hT hb f hf hfT).2.1 o ho c, (hB C S V Q hF hT hb f hf hfT).2.1 o ho c'⟩
  · intro C V S Q f hf hb hT hfT hF c c' o o' ho ho'
    rw [← (hB C S V Q hF hT hb f hf hfT).2.2 c' c o' o ho' ho]
    exact ⟨fun ⟨O, hO, e1, e2⟩ => ⟨O, hO, e2, e1⟩, fun ⟨O, hO, e1, e2⟩ => ⟨O, hO, e2, e1⟩⟩

theorem A_to_B : A → B := fun h => main_to_B ⟨h.1, h.2.1, h.2.2.1⟩

theorem B_to_A : B → A := by
  intro hB
  obtain ⟨h1, h2, h3⟩ := B_to_main hB
  exact ⟨h1, h2, h3, reflectionConstruction_isTame, reflection_admitsModelBumpFunctions,
    isScFredholmSectionFunctor_reflDiag, isScFredholmSectionFunctorTame_reflDiag,
    reflQ_hasStrongBundleUniformizers, reflDiag_nondegenerate.1, reflDiag_nondegenerate.2.1⟩

#rt_check RoundTrip.V18_49.A_to_B
  [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_5_6_one_hyp,
   Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_5_6_two_hyp,
   Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_5_6_three_hyp,
   Polyfold.GCT.VectorBundle.ReflectionBundle.reflDiag_orientation_hyp]
#rt_check RoundTrip.V18_49.B_to_A
  [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_5_6_one_hyp,
   Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_5_6_two_hyp,
   Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_5_6_three_hyp,
   Polyfold.GCT.VectorBundle.ReflectionBundle.reflDiag_orientation_hyp]
#rt_check RoundTrip.V18_49.main_to_B
  [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_5_6_one_hyp,
   Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_5_6_two_hyp,
   Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_5_6_three_hyp,
   Polyfold.GCT.VectorBundle.ReflectionBundle.reflDiag_orientation_hyp]
#rt_check RoundTrip.V18_49.B_to_main
  [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_5_6_one_hyp,
   Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_5_6_two_hyp,
   Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_5_6_three_hyp,
   Polyfold.GCT.VectorBundle.ReflectionBundle.reflDiag_orientation_hyp]
#rt_overlap RoundTrip.V18_49.B_to_A
  [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_5_6_one_hyp,
   Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_5_6_two_hyp,
   Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.proposition_18_5_6_three_hyp,
   Polyfold.GCT.VectorBundle.ReflectionBundle.reflDiag_orientation_hyp]

end RoundTrip.V18_49
