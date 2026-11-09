import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_41

/-!
Round trip for V4_41 (Theorem 4.18).  `A` is the conjunction of the types of
`Polyfold.MPolyfold.theorem_4_2_7`, `Polyfold.MPolyfold.hasCornerStructure_of_centred_isInGoodPosition`
and `Polyfold.MPolyfold.IsGoodPositionAt.isInGoodPosition_of_tame`, universe instantiated at `0`.

Glue for `A → B`: B existentially provides the paracompactness of `A` (an instance argument of
the induced structure); every subset of an M-polyfold is paracompact
(`MPolyfold.paracompactSpace_subtype`, from metrizability, Theorem 2.16).  The induced structure
does not depend on the proofs (proof irrelevance), and `IsTameSubmanifold A` unfolds to B's
`(subPolyfold hA).IsTame`.

`B → A` is proved only for the first conjunct (`theorem_4_2_7`, `B_to_A_main`): the other two are
lemmas of the proof with hypotheses B does not cover (no tameness of `X`, a chart-wise good
position hypothesis in an arbitrary centred chart; resp. the conclusion that a specific tangent
space is in good position in a specific tame chart), which B does not mention.
-/

namespace RoundTrip.V4_41
open Polyfold

/-- The project's statement, universe `0`. -/
def A : Prop :=
  type_of% @Polyfold.MPolyfold.theorem_4_2_7.{0} ∧
    type_of% @Polyfold.MPolyfold.hasCornerStructure_of_centred_isInGoodPosition.{0} ∧
    type_of% @Polyfold.MPolyfold.IsGoodPositionAt.isInGoodPosition_of_tame.{0}

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.theorem_4_2_7.{0},
    @Polyfold.MPolyfold.hasCornerStructure_of_centred_isInGoodPosition.{0},
    @Polyfold.MPolyfold.IsGoodPositionAt.isInGoodPosition_of_tame.{0}⟩

theorem A_to_B : A → B := by
  rintro ⟨h418, -, -⟩ X _ _ _ P S hP hS hgp
  have : ParacompactSpace S := P.paracompactSpace_subtype S
  obtain ⟨hcs, hS', htame⟩ := h418 hP hS hgp
  exact ⟨hS.isSubMPolyfold, inferInstance, hcs, htame⟩

/-- B gives the main conjunct of A (Theorem 4.18 itself). -/
theorem B_to_A_main : B → type_of% @Polyfold.MPolyfold.theorem_4_2_7.{0} := by
  intro hB X _ _ _ P hP S hS _ hgp
  obtain ⟨_, _, hcs, htame⟩ := hB X P S hP hS hgp
  exact ⟨hcs, hS, htame⟩

#rt_check RoundTrip.V4_41.A_to_B [Polyfold.MPolyfold.theorem_4_2_7,
  Polyfold.MPolyfold.hasCornerStructure_of_centred_isInGoodPosition,
  Polyfold.MPolyfold.IsGoodPositionAt.isInGoodPosition_of_tame]
#rt_check RoundTrip.V4_41.B_to_A_main [Polyfold.MPolyfold.theorem_4_2_7,
  Polyfold.MPolyfold.hasCornerStructure_of_centred_isInGoodPosition,
  Polyfold.MPolyfold.IsGoodPositionAt.isInGoodPosition_of_tame]
#rt_overlap RoundTrip.V4_41.B_to_A_main [Polyfold.MPolyfold.theorem_4_2_7,
  Polyfold.MPolyfold.hasCornerStructure_of_centred_isInGoodPosition,
  Polyfold.MPolyfold.IsGoodPositionAt.isInGoodPosition_of_tame]

end RoundTrip.V4_41
