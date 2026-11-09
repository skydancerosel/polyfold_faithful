import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_11

/-! Round trip for V8_11 (Lemma 8.1.9 (2017: 8.8): `TX` is tame if `X` is).

`A` is the conjunction of the types of the twelve listed theorems (`ScIso.tangentPres` is a
definition, vocabulary), universes instantiated at `0` where there are any (`B` lives in `Type`):

1. `tangentSet_eq_tangentPres`, 2. `degIndex_tangentSet`, 3. `mem_minimalSubspaceWith_tangentPres`
   (the presentation `T'` of `TC = C¹ ⊕ E`);
4. `ScRetraction.scDeriv_tangentRetraction_fst`, 5. `…_inr` (the derivative of `Tr`);
6. `ScRetraction.IsTameWith.tangent`, 7. `ScRetraction.IsTame.tangentRetraction`,
   8. `IsTameRetract.tangent` (`Tr` is a tame retraction);
9. `MPolyfold.IsTame.tangent` (`P` tame ⇒ `TP` tame, for every M-polyfold);
10. `EpGroupoid.lemma_8_8` (`X` tame ⇒ `TX` tame);
11. `EpGroupoid.isTame_tangentEpGroupoid_trivial_rn` (satisfiability witness);
12. `ScRetraction.IsTameWith.isTame` (Part I, Lemma 1.24: presentation independence).

`B`: for every ep-groupoid `X` in `Type`, `X.PObj.IsTame → X.PObj.tangentPolyfold.IsTame`.

* `A_to_B` from conjunct 9 (or 10: `EpGroupoid.IsTame` is tameness of the object M-polyfold and
  the object M-polyfold of `tangentEpGroupoid` is `tangentPolyfold`).
* `B_to_A` fails: conjuncts 1–8 and 12 are retraction-level lemmas of the proof (sc-isomorphisms
  presenting `TC`, derivatives of `Tr`, tame retracts, presentation independence) about which `B`
  says nothing.  `B_to_A_main` proves the M-polyfold / ep-groupoid conjuncts 9–11 from `B`
  (conjunct 9 through the trivial ep-groupoid of `P`). -/

namespace RoundTrip.V8_11
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.tangentSet_eq_tangentPres) ∧
  (type_of% @Polyfold.degIndex_tangentSet) ∧
  (type_of% @Polyfold.mem_minimalSubspaceWith_tangentPres) ∧
  (type_of% @Polyfold.ScRetraction.scDeriv_tangentRetraction_fst) ∧
  (type_of% @Polyfold.ScRetraction.scDeriv_tangentRetraction_inr) ∧
  (type_of% @Polyfold.ScRetraction.IsTameWith.tangent) ∧
  (type_of% @Polyfold.ScRetraction.IsTame.tangentRetraction) ∧
  (type_of% @Polyfold.IsTameRetract.tangent) ∧
  (type_of% @Polyfold.MPolyfold.IsTame.tangent.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.lemma_8_8.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isTame_tangentEpGroupoid_trivial_rn) ∧
  (type_of% @Polyfold.ScRetraction.IsTameWith.isTame)

theorem A_holds : A :=
  ⟨@Polyfold.tangentSet_eq_tangentPres, @Polyfold.degIndex_tangentSet,
    @Polyfold.mem_minimalSubspaceWith_tangentPres,
    @Polyfold.ScRetraction.scDeriv_tangentRetraction_fst,
    @Polyfold.ScRetraction.scDeriv_tangentRetraction_inr,
    @Polyfold.ScRetraction.IsTameWith.tangent, @Polyfold.ScRetraction.IsTame.tangentRetraction,
    @Polyfold.IsTameRetract.tangent, @Polyfold.MPolyfold.IsTame.tangent.{0},
    @Polyfold.EpGroupoid.lemma_8_8.{0}, @Polyfold.EpGroupoid.isTame_tangentEpGroupoid_trivial_rn,
    @Polyfold.ScRetraction.IsTameWith.isTame⟩

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X hX
  obtain ⟨-, -, -, -, -, -, -, -, h9, -⟩ := hA
  exact h9 hX

/-- The M-polyfold and ep-groupoid conjuncts 9–11 of `A`. -/
def AMain : Prop :=
  (type_of% @Polyfold.MPolyfold.IsTame.tangent.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.lemma_8_8.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isTame_tangentEpGroupoid_trivial_rn)

/-- `B` gives conjuncts 9–11 of `A`: conjunct 9 by applying `B` to the trivial ep-groupoid of
`P` (whose object M-polyfold is `P`), conjunct 10 since `EpGroupoid.IsTame` is tameness of the
object M-polyfold, conjunct 11 from 10 and Chapter 7's `isTame_trivial_rn`. -/
theorem B_to_A_main : B → AMain := by
  intro hB
  have h10 : type_of% @Polyfold.EpGroupoid.lemma_8_8.{0} :=
    fun X hX => hB _ _ X hX
  refine ⟨fun {Z} _ _ _ {P} _ hP => hB Z Z (EpGroupoid.trivial P) hP, h10, fun n => ?_⟩
  exact h10 _ (EpGroupoid.isTame_trivial_rn n)

#rt_check RoundTrip.V8_11.A_to_B [Polyfold.tangentSet_eq_tangentPres,
  Polyfold.degIndex_tangentSet, Polyfold.mem_minimalSubspaceWith_tangentPres,
  Polyfold.ScRetraction.scDeriv_tangentRetraction_fst,
  Polyfold.ScRetraction.scDeriv_tangentRetraction_inr, Polyfold.ScRetraction.IsTameWith.tangent,
  Polyfold.ScRetraction.IsTame.tangentRetraction, Polyfold.IsTameRetract.tangent,
  Polyfold.MPolyfold.IsTame.tangent, Polyfold.EpGroupoid.lemma_8_8,
  Polyfold.EpGroupoid.isTame_tangentEpGroupoid_trivial_rn, Polyfold.ScRetraction.IsTameWith.isTame]
#rt_check RoundTrip.V8_11.B_to_A_main [Polyfold.tangentSet_eq_tangentPres,
  Polyfold.degIndex_tangentSet, Polyfold.mem_minimalSubspaceWith_tangentPres,
  Polyfold.ScRetraction.scDeriv_tangentRetraction_fst,
  Polyfold.ScRetraction.scDeriv_tangentRetraction_inr, Polyfold.ScRetraction.IsTameWith.tangent,
  Polyfold.ScRetraction.IsTame.tangentRetraction, Polyfold.IsTameRetract.tangent,
  Polyfold.MPolyfold.IsTame.tangent, Polyfold.EpGroupoid.lemma_8_8,
  Polyfold.EpGroupoid.isTame_tangentEpGroupoid_trivial_rn, Polyfold.ScRetraction.IsTameWith.isTame]
#rt_overlap RoundTrip.V8_11.B_to_A_main [Polyfold.tangentSet_eq_tangentPres,
  Polyfold.degIndex_tangentSet, Polyfold.mem_minimalSubspaceWith_tangentPres,
  Polyfold.ScRetraction.scDeriv_tangentRetraction_fst,
  Polyfold.ScRetraction.scDeriv_tangentRetraction_inr, Polyfold.ScRetraction.IsTameWith.tangent,
  Polyfold.ScRetraction.IsTame.tangentRetraction, Polyfold.IsTameRetract.tangent,
  Polyfold.MPolyfold.IsTame.tangent, Polyfold.EpGroupoid.lemma_8_8,
  Polyfold.EpGroupoid.isTame_tangentEpGroupoid_trivial_rn, Polyfold.ScRetraction.IsTameWith.isTame]

end RoundTrip.V8_11
