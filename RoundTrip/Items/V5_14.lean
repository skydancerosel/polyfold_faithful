import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_14_r2

/-! Round trip for V5_14 (Corollary 5.8, "it is a priori clear that `f^i` is sc-Fredholm", as a
section of `P^i : Y^i → X^i`), against the second blind statement `RoundTrip.V5_14_r2.B`
(`RoundTrip/Blind/V5_14_r2.lean`).

A = the types of the twelve theorems among the decls (universes at `0`):
`StrongBundleChart.Compatible.shift`, `StrongBundle.mem_shift_doubleLevel_iff`,
`StrongBundle.regularizing_sectionShift`, `IsSc0ContractionGerm.shift`, `IsBasicGerm.shift`,
`IsConjugateToBasicGerm.shift`, `IsConjugateToBasicGerm.shift_germ`,
`IsFillingGerm.mem_range_toBase_of_fillDefect`, `IsFillingGerm.germ_shift`,
`isScFredholmGerm_sectionShift`, `corollary_5_8_isScFredholmSection`, `corollary_5_8_chart`.
`StrongBundle.shift`, `StrongBundleChart.shift`, `StrongBundle.sectionShift`,
`ScNbhdGerm.shiftParam` are vocabulary (B uses the first and third ones, through `Data.shift`).

B: for every sc-Fredholm section `f` (germ reading) of a strong bundle `P` (no tameness, no
compactness) and every `i`, the iterated index raise `f^i` (`Data.iter`: `P^{i+1} = (P^i).shift`,
`f^{i+1} = (P^i).sectionShift f^i`) is an sc-Fredholm section of `P^i`.

* `A ⇒ B` is proved (`A_to_B`): induction on `i`, the step being A's
  `corollary_5_8_isScFredholmSection` applied to the bundle `P^i` (the hypothesis, not the
  project theorem).  Checked with `#rt_check_soft`: `Compatible.shift` is reached only through
  the proof fields of `StrongBundle.shiftAtlas` (the atlas of `P¹`, which B's own `Data.shift`
  uses); plain `#rt_check` fails only for that reason.
* `B ⇒ A` fails: B gives A's `corollary_5_8_isScFredholmSection` (its `i = 1` case,
  `B_gives_isScFredholmSection`), but the other eleven conjuncts are auxiliary lemmas about
  arbitrary germs, retractions, charts and (merely sc-smooth / regularizing) sections
  (`Compatible.shift`, `mem_shift_doubleLevel_iff`, `regularizing_sectionShift`,
  `IsSc0ContractionGerm.shift`, `IsBasicGerm.shift`, `IsConjugateToBasicGerm.shift(_germ)`,
  `IsFillingGerm.*`, `isScFredholmGerm_sectionShift` for an sc-smooth `f` with a germ at one
  point), and `corollary_5_8_chart` contains the compactness of the level-`1` solution set and the
  index raise of the germ data in the ORIGINAL chart `Φ`; none of these is about B's objects. -/

namespace RoundTrip.V5_14
open Polyfold

/-- The project's statement, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.StrongBundleChart.Compatible.shift.{0, 0} ∧
  type_of% @Polyfold.StrongBundle.mem_shift_doubleLevel_iff.{0, 0} ∧
  type_of% @Polyfold.StrongBundle.regularizing_sectionShift.{0, 0} ∧
  type_of% @Polyfold.IsSc0ContractionGerm.shift ∧
  type_of% @Polyfold.IsBasicGerm.shift ∧
  type_of% @Polyfold.IsConjugateToBasicGerm.shift ∧
  type_of% @Polyfold.IsConjugateToBasicGerm.shift_germ ∧
  type_of% @Polyfold.IsFillingGerm.mem_range_toBase_of_fillDefect ∧
  type_of% @Polyfold.IsFillingGerm.germ_shift ∧
  type_of% @Polyfold.isScFredholmGerm_sectionShift.{0, 0} ∧
  type_of% @Polyfold.corollary_5_8_isScFredholmSection.{0, 0} ∧
  type_of% @Polyfold.corollary_5_8_chart.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.StrongBundleChart.Compatible.shift.{0, 0},
    @Polyfold.StrongBundle.mem_shift_doubleLevel_iff.{0, 0},
    @Polyfold.StrongBundle.regularizing_sectionShift.{0, 0}, @Polyfold.IsSc0ContractionGerm.shift,
    @Polyfold.IsBasicGerm.shift, @Polyfold.IsConjugateToBasicGerm.shift,
    @Polyfold.IsConjugateToBasicGerm.shift_germ,
    @Polyfold.IsFillingGerm.mem_range_toBase_of_fillDefect, @Polyfold.IsFillingGerm.germ_shift,
    @Polyfold.isScFredholmGerm_sectionShift.{0, 0},
    @Polyfold.corollary_5_8_isScFredholmSection.{0, 0}, @Polyfold.corollary_5_8_chart.{0, 0}⟩

/-- One index raise, from A's `corollary_5_8_isScFredholmSection`. -/
theorem step (hA : A) (D : V5_14_r2.Data) (h : D.Bd.IsScFredholmSection D.f) :
    D.shift.Bd.IsScFredholmSection D.shift.f :=
  hA.2.2.2.2.2.2.2.2.2.2.1 h

/-- Every index raise, by induction. -/
theorem iter (hA : A) (D : V5_14_r2.Data) (h : D.Bd.IsScFredholmSection D.f) :
    ∀ i, (D.iter i).Bd.IsScFredholmSection (D.iter i).f
  | 0 => h
  | i + 1 => step hA (D.iter i) (iter hA D h i)

theorem A_to_B : A → V5_14_r2.B := by
  intro hA X _ _ _ PX Y _ _ _ P _ _ Bd f hf i D
  exact iter hA D hf i

/-- B gives A's central conjunct `corollary_5_8_isScFredholmSection` (its case `i = 1`). -/
theorem B_gives_isScFredholmSection (hB : V5_14_r2.B) :
    type_of% @Polyfold.corollary_5_8_isScFredholmSection.{0, 0} := by
  intro X _ _ _ PX Y _ _ _ P _ _ Bd f hf
  exact hB PX P Bd f hf 1

#rt_check_soft RoundTrip.V5_14.A_to_B [Polyfold.StrongBundleChart.Compatible.shift,
  Polyfold.StrongBundle.mem_shift_doubleLevel_iff, Polyfold.StrongBundle.regularizing_sectionShift,
  Polyfold.IsSc0ContractionGerm.shift, Polyfold.IsBasicGerm.shift,
  Polyfold.IsConjugateToBasicGerm.shift, Polyfold.IsConjugateToBasicGerm.shift_germ,
  Polyfold.IsFillingGerm.mem_range_toBase_of_fillDefect, Polyfold.IsFillingGerm.germ_shift,
  Polyfold.isScFredholmGerm_sectionShift, Polyfold.corollary_5_8_isScFredholmSection,
  Polyfold.corollary_5_8_chart]
#rt_check_soft RoundTrip.V5_14.B_gives_isScFredholmSection [Polyfold.StrongBundleChart.Compatible.shift,
  Polyfold.StrongBundle.mem_shift_doubleLevel_iff, Polyfold.StrongBundle.regularizing_sectionShift,
  Polyfold.IsSc0ContractionGerm.shift, Polyfold.IsBasicGerm.shift,
  Polyfold.IsConjugateToBasicGerm.shift, Polyfold.IsConjugateToBasicGerm.shift_germ,
  Polyfold.IsFillingGerm.mem_range_toBase_of_fillDefect, Polyfold.IsFillingGerm.germ_shift,
  Polyfold.isScFredholmGerm_sectionShift, Polyfold.corollary_5_8_isScFredholmSection,
  Polyfold.corollary_5_8_chart]
#rt_overlap RoundTrip.V5_14.B_gives_isScFredholmSection [Polyfold.StrongBundleChart.Compatible.shift,
  Polyfold.StrongBundle.mem_shift_doubleLevel_iff, Polyfold.StrongBundle.regularizing_sectionShift,
  Polyfold.IsSc0ContractionGerm.shift, Polyfold.IsBasicGerm.shift,
  Polyfold.IsConjugateToBasicGerm.shift, Polyfold.IsConjugateToBasicGerm.shift_germ,
  Polyfold.IsFillingGerm.mem_range_toBase_of_fillDefect, Polyfold.IsFillingGerm.germ_shift,
  Polyfold.isScFredholmGerm_sectionShift, Polyfold.corollary_5_8_isScFredholmSection,
  Polyfold.corollary_5_8_chart]

end RoundTrip.V5_14
