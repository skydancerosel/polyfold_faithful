import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_56

/-! Round trip for V10_56 (2021 Definition 10.5.2, p. 506; 2017: Definition 10.15, p. 366:
generalized strong bundle isomorphisms).

The item lists the definitions `GenSBMap.IsGeneralizedIso`, `SDiagram.symm` and `negDiagram`
(vocabulary) and three theorems; `A` is the conjunction of their types, universes at `0`
(`isGeneralizedIso_negDiagram` has none, it lives at `0`): `isGeneralizedIso_symm` (the reversed
diagram of a representative with both legs equivalences is one), `isGeneralizedIso_ofHom`
(`[W ←1 W →Ψ W']` for a strong bundle equivalence `Ψ`) and `isGeneralizedIso_negDiagram` (a
non-trivial example).

`B` says that the project's `IsGeneralizedIso f` is "`f = [D]` for a diagram whose two legs are
strong bundle equivalences".

* `A_to_B`: `B` holds by the definitions (the project's `IsGeneralizedIso` asks only for `Ψ`, since
  `Φ` is a strong bundle equivalence in every `SDiagram`, the field `isEquivalence_Φ`; and
  `SEP.equivalences F` unfolds to `IsStrongBundleEquivalence` of `(ϕ, Φ)`).  It is proved outright,
  without the hypothesis: `A`'s three theorems are instances, not the definition.
* `B_to_A`: each of `A`'s three theorems is `B`'s `←` applied to the diagram in question
  (`negSEPHom_mem_equivalences`, a non-item lemma, for the example). -/

namespace RoundTrip.V10_56
open Polyfold CategoryTheory

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.SBLocalization.GenSBMap.isGeneralizedIso_symm.{0}) ∧
  (type_of% @Polyfold.SBLocalization.GenSBMap.isGeneralizedIso_ofHom.{0}) ∧
  (type_of% @Polyfold.StrongBundleLocalizationExamples.isGeneralizedIso_negDiagram)

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.GenSBMap.isGeneralizedIso_symm.{0},
    @Polyfold.SBLocalization.GenSBMap.isGeneralizedIso_ofHom.{0},
    @Polyfold.StrongBundleLocalizationExamples.isGeneralizedIso_negDiagram⟩

/-- `B` is the project's definition unfolded; proved outright (the hypothesis is not used). -/
theorem A_to_B : A → B := by
  intro _ A A' f
  constructor
  · rintro ⟨D, hD, hΨ⟩
    exact ⟨D, hD, D.isEquivalence_Φ, hΨ⟩
  · rintro ⟨D, hD, -, hΨ⟩
    exact ⟨D, hD, hΨ⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun {A A'} D hΨ => (hB _ _ _).2 ⟨D.symm hΨ, rfl, hΨ, D.isEquivalence_Φ⟩,
    fun {A A' Ψ} hΨ => (hB _ _ _).2
      ⟨SBLocalization.SDiagram.ofHom Ψ, rfl, SEP.equivalences.id_mem A, hΨ⟩,
    fun n k => (hB _ _ _).2 ⟨StrongBundleLocalizationExamples.negDiagram n k, rfl,
      SEP.equivalences.id_mem _, StrongBundleEquivalenceExamples.negSEPHom_mem_equivalences n k⟩⟩

#rt_check RoundTrip.V10_56.A_to_B [Polyfold.SBLocalization.GenSBMap.isGeneralizedIso_symm,
  Polyfold.SBLocalization.GenSBMap.isGeneralizedIso_ofHom,
  Polyfold.StrongBundleLocalizationExamples.isGeneralizedIso_negDiagram]
#rt_check RoundTrip.V10_56.B_to_A [Polyfold.SBLocalization.GenSBMap.isGeneralizedIso_symm,
  Polyfold.SBLocalization.GenSBMap.isGeneralizedIso_ofHom,
  Polyfold.StrongBundleLocalizationExamples.isGeneralizedIso_negDiagram]
#rt_overlap RoundTrip.V10_56.B_to_A [Polyfold.SBLocalization.GenSBMap.isGeneralizedIso_symm,
  Polyfold.SBLocalization.GenSBMap.isGeneralizedIso_ofHom,
  Polyfold.StrongBundleLocalizationExamples.isGeneralizedIso_negDiagram]

end RoundTrip.V10_56
