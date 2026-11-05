import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_60

/-! Round trip for V2_60 (Definition 2.53: the pull-back `f*Y`, `P_f`, `P'`, `P ∘ P' = f ∘ P_f`).

`A` is the conjunction of the types of the theorems `pullback_comm`, `continuous_pullbackProj`
and `isClosed_pullbackSpace`, at universes `0, 0, 0`.  `pullbackSpace`, `pullbackProj`,
`pullbackProj'` are definitions (vocabulary).

`A → B` (proved): `pullbackSpace P f` is B's `{(z, y) | P y = f z}` and its topology is the
subspace topology, both definitionally; the projections agree definitionally; `P ∘ P' = f ∘ P_f`
is `pullback_comm` (the hypothesis).

`B → A` fails: B states the identity `P ∘ P' = f ∘ P_f` only in the text's setting (`X`, `Z`
M-polyfolds, `P` a strong bundle, `f` sc-smooth), while `pullback_comm` holds for arbitrary maps
of arbitrary types; and `continuous_pullbackProj` (`P_f` continuous) and
`isClosed_pullbackSpace` (`f*Y` closed in `Z × Y` for continuous `P`, `f`, `X` Hausdorff) are not
in B at all.  These are true elementary topological facts that the item's text does not state. -/

namespace RoundTrip.V2_60
open Polyfold Set

/-- The project's statement (universes `0`). -/
def A : Prop :=
  (type_of% @Polyfold.pullback_comm.{0, 0, 0}) ∧
    (type_of% @Polyfold.continuous_pullbackProj.{0, 0, 0}) ∧
    (type_of% @Polyfold.isClosed_pullbackSpace.{0, 0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.pullback_comm.{0, 0, 0}, @Polyfold.continuous_pullbackProj.{0, 0, 0},
    @Polyfold.isClosed_pullbackSpace.{0, 0, 0}⟩

theorem A_to_B : A → B := by
  rintro ⟨hcomm, -, -⟩ X _ _ _ PX Y _ P _ _ _ _ Z _ _ _ PZ _Bd f _
  refine ⟨rfl, rfl, fun w w' h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩, hcomm P f⟩

#rt_check RoundTrip.V2_60.A_to_B [Polyfold.pullback_comm, Polyfold.continuous_pullbackProj,
  Polyfold.isClosed_pullbackSpace]

end RoundTrip.V2_60
