import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_31

/-! Round trip for V10_31 (2021 Definition 10.4.11, p. 503; 2017: Definition 10.13, p. 364:
the category `𝓢𝓔𝓟` and its class `F` of strong bundle equivalences).

The listed `SEP`, `SEP.Hom`, `SEP.equivalences`, `SEP.toEP` and
`StrongBundleEquivalenceExamples.negSEPHom` are definitions (vocabulary).  `A` is the
conjunction of the types of the two listed theorems, universe at `0` (`B` lives in `SEP.{0}`):
`SEP.toEP_map_mem_equivalences` (the forgetful functor `SEP → EP` maps `F` into `E`) and
`negSEPHom_mem_equivalences` (no universe parameters: the projection `(-id)*W' → W'` of the
trivial bundle `ℝⁿ × ℝᵏ → ℝⁿ` lies in `F`).

The text's statement is a definition, and B is the claim that the project's definitions are the
text's: B is proved outright (`B_holds`), with `e` the obvious repackaging of a `SEP.Hom`
(a structure with fields `ϕ`, `Φ`, `isStrongBundleFunctor`) as B's subtype of pairs; the
identities and composites of the project's `LargeCategory SEP` are the pairs of identity
functors and the componentwise composites (`rfl`), and `SEP.equivalences f` *is*
`IsStrongBundleEquivalence f.ϕ f.Φ` (`Iff.rfl`).

* `A_to_B` is `B_holds`; it does not use `A` (vacuous).
* `B_to_A` re-proves `A` outright, without `B`: the first conjunct is the field
  `isEquivalence_base` of `IsStrongBundleEquivalence` (the project's one-line proof), the second
  is `isStrongBundleEquivalence_pullbackProj'` (the project's lemma on which
  `negSEPHom_mem_equivalences` rests).  `B` cannot supply either: its bijection `e` is arbitrary,
  so `B` does not identify `(e f).1.1` with `toEP.map f`, and `B` says nothing about examples
  (vacuous). -/

namespace RoundTrip.V10_31
open Polyfold CategoryTheory

/-- The project's statement (universe at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.SEP.toEP_map_mem_equivalences.{0}) ∧
  (type_of% @Polyfold.StrongBundleEquivalenceExamples.negSEPHom_mem_equivalences)

theorem A_holds : A :=
  ⟨@Polyfold.SEP.toEP_map_mem_equivalences.{0},
    @Polyfold.StrongBundleEquivalenceExamples.negSEPHom_mem_equivalences⟩

/-- A morphism of the project's `SEP` is B's pair `(ϕ, Φ)` with `Φ` a strong bundle functor
covering `ϕ`. -/
def e (A A' : SEP.{0}) : (A ⟶ A') ≃ HomB A A' where
  toFun f := ⟨(SEP.Hom.ϕ f, SEP.Hom.Φ f), SEP.Hom.isStrongBundleFunctor f⟩
  invFun p := ⟨p.1.1, p.1.2, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The project's definitions are the text's** (B proved outright). -/
theorem B_holds : B :=
  ⟨e, fun _ => ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩,
    fun _ _ _ _ _ => ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩,
    fun _ _ _ => Iff.rfl⟩

theorem A_to_B : A → B := fun _ => B_holds

theorem B_to_A : B → A := fun _ =>
  ⟨fun hF => hF.isEquivalence_base,
    fun n k => StrongBundleEquivalenceExamples.isStrongBundleEquivalence_pullbackProj' n k⟩

#rt_check RoundTrip.V10_31.A_to_B [Polyfold.SEP.toEP_map_mem_equivalences,
  Polyfold.StrongBundleEquivalenceExamples.negSEPHom_mem_equivalences]
#rt_check RoundTrip.V10_31.B_to_A [Polyfold.SEP.toEP_map_mem_equivalences,
  Polyfold.StrongBundleEquivalenceExamples.negSEPHom_mem_equivalences]
#rt_overlap RoundTrip.V10_31.B_to_A [Polyfold.SEP.toEP_map_mem_equivalences,
  Polyfold.StrongBundleEquivalenceExamples.negSEPHom_mem_equivalences]
#rt_check RoundTrip.V10_31.B_holds [Polyfold.SEP.toEP_map_mem_equivalences,
  Polyfold.StrongBundleEquivalenceExamples.negSEPHom_mem_equivalences]

end RoundTrip.V10_31
