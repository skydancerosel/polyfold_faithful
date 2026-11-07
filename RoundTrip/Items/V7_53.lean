import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_53

/-!
Round trip for V7_53 (Definition 7.15, the sentence before Remark 7.1, Remark 7.1).

`A` is the conjunction of the types of the three listed theorems (universes at `0`):
`remark_7_1` (second countable object space ⇒ `|X|` paracompact),
`hasParacompactOrbitSpace_of_secondCountableTopology` (second countable `|X|` ⇒ paracompact) and
`hasParacompactOrbitSpace_iff_metrizableSpace` (`|X|` paracompact ⇔ metrizable, Theorem 7.2).
The listed definition `HasParacompactOrbitSpace` is `ParacompactSpace X.OrbitSpace`, whose single
field is literally B's `IsParacompactB` (index types in `Type`), so B's first conjunct is proved
outright (`defn_iff`).

* `A → B`: `defn_iff` and `remark_7_1` (from the hypothesis).
* `B → A`: `remark_7_1` is B's second conjunct (via `defn_iff`).  The other two conjuncts of `A` are
  not in `B` (nor in the text's Definition 7.15 paragraph): they are proved outright from the
  unbanned `corollary_7_1` (second countable `|X|` ⇒ metrizable), `theorem_7_2_metrizable`
  (paracompact `|X|` ⇒ metrizable, Theorem 7.2) and Stone's theorem.
-/

namespace RoundTrip.V7_53
open Polyfold

/-- The listed theorems (universes at `0`). -/
def A : Prop :=
  type_of% @Polyfold.EpGroupoid.remark_7_1.{0} ∧
  type_of% @Polyfold.EpGroupoid.hasParacompactOrbitSpace_of_secondCountableTopology.{0} ∧
  type_of% @Polyfold.EpGroupoid.hasParacompactOrbitSpace_iff_metrizableSpace.{0}

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.remark_7_1.{0},
    @Polyfold.EpGroupoid.hasParacompactOrbitSpace_of_secondCountableTopology.{0},
    @Polyfold.EpGroupoid.hasParacompactOrbitSpace_iff_metrizableSpace.{0}⟩

/-- Mathlib's `ParacompactSpace` (for a space in `Type`) is B's paracompactness. -/
theorem paracompact_iff (T : Type) [TopologicalSpace T] :
    ParacompactSpace T ↔ IsParacompactB T :=
  ⟨fun h => h.locallyFinite_refinement, fun h => ⟨h⟩⟩

/-- B's first conjunct: Definition 7.15 is the text's. -/
theorem defn_iff {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor) :
    X.HasParacompactOrbitSpace ↔ IsParacompactB X.OrbitSpace :=
  paracompact_iff X.OrbitSpace

theorem A_to_B : A → B := by
  rintro ⟨h1, -, -⟩
  refine ⟨fun Obj Mor _ _ _ _ _ _ X => defn_iff X, fun Obj Mor _ _ _ _ _ _ X hsc => ?_⟩
  exact (defn_iff X).1 (h1 X)

theorem B_to_A : B → A := by
  rintro ⟨-, h2⟩
  refine ⟨fun {Obj Mor} _ _ _ _ _ _ X _ => (defn_iff X).2 (h2 Obj Mor X inferInstance), ?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X _
    have := X.corollary_7_1
    exact paracompactSpace_of_metrizableSpace _
  · intro Obj Mor _ _ _ _ _ _ X
    exact ⟨X.theorem_7_2_metrizable, fun _ => paracompactSpace_of_metrizableSpace _⟩

#rt_check RoundTrip.V7_53.A_to_B [Polyfold.EpGroupoid.remark_7_1,
  Polyfold.EpGroupoid.hasParacompactOrbitSpace_of_secondCountableTopology,
  Polyfold.EpGroupoid.hasParacompactOrbitSpace_iff_metrizableSpace]
#rt_check RoundTrip.V7_53.B_to_A [Polyfold.EpGroupoid.remark_7_1,
  Polyfold.EpGroupoid.hasParacompactOrbitSpace_of_secondCountableTopology,
  Polyfold.EpGroupoid.hasParacompactOrbitSpace_iff_metrizableSpace]
#rt_overlap RoundTrip.V7_53.B_to_A [Polyfold.EpGroupoid.remark_7_1,
  Polyfold.EpGroupoid.hasParacompactOrbitSpace_of_secondCountableTopology,
  Polyfold.EpGroupoid.hasParacompactOrbitSpace_iff_metrizableSpace]

end RoundTrip.V7_53
