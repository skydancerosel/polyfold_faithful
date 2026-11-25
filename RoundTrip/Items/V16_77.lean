import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V16_77

set_option maxSynthPendingDepth 3

/-! Round trip for V16_77 (2021 Definition 16.6.5, p. 739; 2017: Definition 16.42: orientations of
sc-Fredholm sections, transported by Theorem 12.5.7).

The item lists ten definitions (vocabulary: `OrientationRep`, `FredholmSection.IsOrientable`,
`OrientationRepLoc` with `toOrientationRep`/`toLoc`, `IsOrientableLoc`, and the example records
`halfOrientationRep`, `halfOrientationRepLoc`, `z3OrientationRep`, `halfZ3OrientationRep`) and
27 theorems; `A` is the conjunction of the theorems' types, universes at `0` (`B` is stated for
`Y Z : Type`; the SEP-level theorems at `SEP.{0}`; the examples have no universe parameter).

Main conjunct: `OrientationRep.exists_unique_transport_of_isLR` (the polyfold-level transport:
for an orientation `R` of `f` and any representative `b` of `f`, assuming that the model of `R` is
tame, admits sc-smooth bump functions and `R.a.F` is tame (Part I's hypotheses), `b.F` is
sc-Fredholm, `b`'s model has sc⁺-sections through every point, and there is exactly one
orientation `o'` of `b.F` whose pull-backs agree with those of `R.o` over every diagram of every
generalized strong bundle isomorphism `𝔄` with `Γ_b ∘ |𝔄| = Γ_R` and `𝔄_* F_R = F_b`).

No direction is proved; see the JSON.  `B`'s clause (0) is the definition of `IsOrientable`
(`B_clause0_holds`, `Iff.rfl`).

* `A ⇒ B` stops at the hypotheses: every transport statement of `A` assumes that the model of the
  given orientation is tame, admits sc-smooth bump functions and carries a tame sc-Fredholm
  section; `B` (1) and (2) assume none of this (and the text's Definition 16.6.5 is stated for a
  *tame* strong polyfold bundle, Theorem 12.5.7 for tame ep-groupoids).  Without these
  hypotheses neither the existence nor the uniqueness of the transport is available in the
  project.  The conclusions also differ in form: `A`'s `o'` is a bare family `x ↦ o'_x`
  characterised by the pull-back equations over *every* diagram of every admissible `𝔄`; `B`'s
  transport is a `Correspondence` (one diagram with `Φ^* o = Ψ^* o'`).  Passing from `A`'s form
  to a `Correspondence` is glue (`exists_diagram`, `pullOr` vs `orEqv`); the hypotheses are not.
* `B ⇒ A` stops because `B` is a statement about strong polyfold bundles and correspondences
  only: it does not give the SEP-level Theorem 12.5.7 (2) (`theorem_12_5_7_two_orbitMap_unique_of_*`),
  the conclusion `∃ hsec' : b`'s model has sc⁺-sections through every point (`B` (1) assumes it),
  the independence of the transported orientation from the diagram and from `𝔄` (`B` (2) speaks
  only of orientations reached through some correspondence), nor the worked examples. -/

namespace RoundTrip.V16_77
open Polyfold

def A : Prop :=
  (type_of% @Polyfold.StrongPolyfoldBundle.OrientationRep.exists_unique_transport_of_isLR.{0})
  ∧ (type_of% @Polyfold.StrongPolyfoldBundle.OrientationRep.exists_unique_transport_of_isLR_polyfold.{0})
  ∧ (type_of% @Polyfold.SBLocalization.GenSBMap.theorem_12_5_7_two_orbitMap_unique_of_isLR.{0})
  ∧ (type_of% @Polyfold.StrongPolyfoldBundle.OrientationRep.exists_unique_transport_of_isLRLocal.{0})
  ∧ (type_of% @Polyfold.StrongPolyfoldBundle.OrientationRep.exists_unique_transport_of_isLRLocal_polyfold.{0})
  ∧ (type_of% @Polyfold.SBLocalization.GenSBMap.theorem_12_5_7_two_orbitMap_unique_of_isLRLocal.{0})
  ∧ (type_of% @Polyfold.StrongPolyfoldBundle.OrientationRep.exists_unique_transport_of_isEffective.{0})
  ∧ (type_of% @Polyfold.StrongPolyfoldBundle.OrientationRep.exists_unique_transport_of_polyfold.{0})
  ∧ (type_of% @Polyfold.StrongPolyfoldBundle.OrientationRep.exists_unique_transport_left.{0})
  ∧ (type_of% @Polyfold.StrongPolyfoldBundle.OrientationRep.transport_left.{0})
  ∧ (type_of% @Polyfold.StrongPolyfoldBundle.OrientationRep.exists_unique_transport.{0})
  ∧ (type_of% @Polyfold.StrongPolyfoldBundle.OrientationRep.transport.{0})
  ∧ (type_of% @Polyfold.SBLocalization.SDiagram.orientation_transport_hyp.{0})
  ∧ (type_of% @Polyfold.SBLocalization.SDiagram.exists_orientation_of_eq.{0})
  ∧ (type_of% @Polyfold.StrongPolyfoldBundle.OrientationRep.exists_diagram.{0})
  ∧ (type_of% @Polyfold.StrongPolyfoldBundle.OrientationRep.transport_hyp.{0})
  ∧ (type_of% @Polyfold.HalfSpaceBundle.exists_unique_transport_halfSpace)
  ∧ (type_of% @Polyfold.HalfSpaceBundle.polyfold_hypotheses_halfSpace)
  ∧ (type_of% @Polyfold.HalfSpaceBundle.exists_unique_transport_halfSpace_of_isLR)
  ∧ (type_of% @Polyfold.StrongBundleLocalizationExamples.exists_unique_transport_z3)
  ∧ (type_of% @Polyfold.StrongBundleLocalizationExamples.theorem_12_5_7_two_orbitMap_unique_z3)
  ∧ (type_of% @Polyfold.StrongBundleLocalizationExamples.exists_unique_transport_z3_of_isLR)
  ∧ (type_of% @Polyfold.StrongPolyfoldBundle.OrientationRep.isSectionOrientation.{0})
  ∧ (type_of% @Polyfold.StrongPolyfoldBundle.FredholmSection.isOrientable_iff_isOrientableLoc.{0})
  ∧ (type_of% @Polyfold.HalfSpaceBundle.isOrientableLoc_halfFredholmSection)
  ∧ (type_of% @Polyfold.HalfSpaceBundle.halfOrientationLoc_witness)
  ∧ (type_of% @Polyfold.HalfSpaceBundle.exists_unique_transport_halfZ3)

theorem A_holds : A :=
  ⟨@Polyfold.StrongPolyfoldBundle.OrientationRep.exists_unique_transport_of_isLR.{0}
  , @Polyfold.StrongPolyfoldBundle.OrientationRep.exists_unique_transport_of_isLR_polyfold.{0}
  , @Polyfold.SBLocalization.GenSBMap.theorem_12_5_7_two_orbitMap_unique_of_isLR.{0}
  , @Polyfold.StrongPolyfoldBundle.OrientationRep.exists_unique_transport_of_isLRLocal.{0}
  , @Polyfold.StrongPolyfoldBundle.OrientationRep.exists_unique_transport_of_isLRLocal_polyfold.{0}
  , @Polyfold.SBLocalization.GenSBMap.theorem_12_5_7_two_orbitMap_unique_of_isLRLocal.{0}
  , @Polyfold.StrongPolyfoldBundle.OrientationRep.exists_unique_transport_of_isEffective.{0}
  , @Polyfold.StrongPolyfoldBundle.OrientationRep.exists_unique_transport_of_polyfold.{0}
  , @Polyfold.StrongPolyfoldBundle.OrientationRep.exists_unique_transport_left.{0}
  , @Polyfold.StrongPolyfoldBundle.OrientationRep.transport_left.{0}
  , @Polyfold.StrongPolyfoldBundle.OrientationRep.exists_unique_transport.{0}
  , @Polyfold.StrongPolyfoldBundle.OrientationRep.transport.{0}
  , @Polyfold.SBLocalization.SDiagram.orientation_transport_hyp.{0}
  , @Polyfold.SBLocalization.SDiagram.exists_orientation_of_eq.{0}
  , @Polyfold.StrongPolyfoldBundle.OrientationRep.exists_diagram.{0}
  , @Polyfold.StrongPolyfoldBundle.OrientationRep.transport_hyp.{0}
  , @Polyfold.HalfSpaceBundle.exists_unique_transport_halfSpace
  , @Polyfold.HalfSpaceBundle.polyfold_hypotheses_halfSpace
  , @Polyfold.HalfSpaceBundle.exists_unique_transport_halfSpace_of_isLR
  , @Polyfold.StrongBundleLocalizationExamples.exists_unique_transport_z3
  , @Polyfold.StrongBundleLocalizationExamples.theorem_12_5_7_two_orbitMap_unique_z3
  , @Polyfold.StrongBundleLocalizationExamples.exists_unique_transport_z3_of_isLR
  , @Polyfold.StrongPolyfoldBundle.OrientationRep.isSectionOrientation.{0}
  , @Polyfold.StrongPolyfoldBundle.FredholmSection.isOrientable_iff_isOrientableLoc.{0}
  , @Polyfold.HalfSpaceBundle.isOrientableLoc_halfFredholmSection
  , @Polyfold.HalfSpaceBundle.halfOrientationLoc_witness
  , @Polyfold.HalfSpaceBundle.exists_unique_transport_halfZ3
  ⟩

/-- `B`'s clause (0) holds by definition (`IsOrientable s := Nonempty (OrientationRep s)`). -/
theorem B_clause0_holds {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
    (c : StrongPolyfoldBundle p) (f : c.FredholmSection) :
    f.IsOrientable ↔ Nonempty (StrongPolyfoldBundle.OrientationRep f) := Iff.rfl

end RoundTrip.V16_77
