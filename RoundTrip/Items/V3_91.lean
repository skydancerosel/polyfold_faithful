import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_91

/-!
Round trip for V3_91 (Theorem 3.18, parametrized perturbations).  `A` is the conjunction of the
types of the theorems among the decls (`paramSection`, `StrongBundle.pullback` are definitions,
vocabulary): `theorem_3_1_21_preprint`, `theorem_3_1_21'`, `paramSection_eq_sectionAdd`,
`StrongBundle.IsScFredholmSection.param`, `StrongBundle.isScPlusSection_paramComb`,
`IsBasicGerm.paramExtend`, `IsConjugateToBasicGerm.paramExtend`, `IsStrongBundleIso.paramMap`,
`prod_rn_isTame`, `isScSmooth_smul`, universes instantiated at `0`.

Refresh 2026-11-02: `theorem_3_1_21_preprint`, `theorem_3_1_21'` and `IsScFredholmSection.param` now state the
germ reading of Definition 3.11 (`IsScFredholmSection` with `IsFillingGerm`, `IsScPlusGerm`), and
so does B's `IsScFredholmSection`; the proof is unchanged.

* `A → B`: `B` is `theorem_3_1_21_preprint` with the extra hypothesis `IsTameStrongBundle Bd` (unused); the
  proof `hπ` of the sc-smoothness of `π` and the section proofs `hf`, `hs` agree with the
  project's by proof irrelevance, the paracompactness instances are arguments of both.
* `B → A` is not proved: `A` assumes no tame strong bundle, and its other conjuncts are lemmas
  (`f̃ = f ∘ π` sc-Fredholm, `s̃` sc⁺, `F = f̃ + s̃`, the `Λ`-extension of basic germs and of
  conjugations, the product strong bundle isomorphism, tameness of `ℝⁿ × X`, sc-smoothness of
  scalar multiplication) that `B` does not state.
-/

namespace RoundTrip.V3_91
open Polyfold

/-- The project's statement, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.theorem_3_1_21_preprint.{0, 0} ∧
    type_of% @Polyfold.theorem_3_1_21'.{0, 0} ∧
    type_of% @Polyfold.paramSection_eq_sectionAdd.{0, 0} ∧
    type_of% @Polyfold.StrongBundle.IsScFredholmSection.param.{0, 0} ∧
    type_of% @Polyfold.StrongBundle.isScPlusSection_paramComb.{0, 0} ∧
    type_of% @Polyfold.IsBasicGerm.paramExtend ∧
    type_of% @Polyfold.IsConjugateToBasicGerm.paramExtend ∧
    type_of% @Polyfold.IsStrongBundleIso.paramMap ∧
    type_of% @Polyfold.prod_rn_isTame.{0} ∧
    type_of% @Polyfold.isScSmooth_smul

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_1_21_preprint.{0, 0}, @Polyfold.theorem_3_1_21'.{0, 0},
    @Polyfold.paramSection_eq_sectionAdd.{0, 0},
    @Polyfold.StrongBundle.IsScFredholmSection.param.{0, 0},
    @Polyfold.StrongBundle.isScPlusSection_paramComb.{0, 0}, @Polyfold.IsBasicGerm.paramExtend,
    @Polyfold.IsConjugateToBasicGerm.paramExtend, @Polyfold.IsStrongBundleIso.paramMap,
    @Polyfold.prod_rn_isTame.{0}, @Polyfold.isScSmooth_smul⟩

theorem A_to_B : A → B := by
  intro hA X _ _ _ PX Y _ _ _ P _ _ Bd n f s _ _ hπ hf hs _ hfF hsP
  exact hA.1 hfF hsP

#rt_check RoundTrip.V3_91.A_to_B [Polyfold.theorem_3_1_21_preprint, Polyfold.theorem_3_1_21',
  Polyfold.paramSection_eq_sectionAdd, Polyfold.StrongBundle.IsScFredholmSection.param,
  Polyfold.StrongBundle.isScPlusSection_paramComb, Polyfold.IsBasicGerm.paramExtend,
  Polyfold.IsConjugateToBasicGerm.paramExtend, Polyfold.IsStrongBundleIso.paramMap,
  Polyfold.prod_rn_isTame, Polyfold.isScSmooth_smul]

end RoundTrip.V3_91
