import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_48

/-! Round trip for V9_48 (Proposition 9.4.10, 2021 p. 435; 2017: Proposition 9.6): comparing
two oriented local branching structures with the same weighted and oriented sums.

`A` is the conjunction of the types of the five listed theorems, universes instantiated at `0`
(`B` lives in `Type`): `EpGroupoid.proposition_9_4_10`, `EpGroupoid.tangent_eq_iff_of_mem_ess`,
and the witnesses `example935_two_le_numClasses`, `example935_hypotheses_9_4_10`,
`example935_MU_eq` (no universe parameters).  `example935B1`, `example935B2` are definitions
(vocabulary).

Neither direction is proved; the difference is genuine.

* The settings differ.  `A` is about two oriented local branching structures on an ep-groupoid
  `X`, with an abstract `SheetGeometry` `G` on `X.PObj` (essential points, null sets, Lemmas
  9.4.4 and 9.4.6 and the tangent note as fields), tangent spaces `X.PObj.submanifoldTangent` and
  oriented tangents `OrTangent` in Part I's tangent bundle.  `B` is about the local model:
  sheets `jᵢ : Nᵢ → F` immersed `n`-manifolds with corners in a Banach space, `T_yMᵢ = Djᵢ(ℝⁿ)`,
  oriented tangents as frame sets in `F` (`posFramesB`), `T̂Θ` a formal sum of those.  The
  project has no ep-groupoid structure on `F` whose tangent objects are `B`'s.
* `A → B` fails.  `B`'s (2) needs, on each piece `A_p`, one subspace `T ⊆ F` with
  `T_yMᵢ = T = T_yM'ᵢ'` for all `i ∈ I_y`, `i' ∈ I'_y`: Lemma 9.4.4 and the tangent note for
  `B`'s sheets, along the chains of `∼_y` of the union structure, which `A` takes as
  `SheetGeometry` fields and states only for `X.PObj.submanifoldTangent`.  `B`'s (4)–(5) need
  that the oriented tangents in `F` of the sheets through `y` are the two orientations
  `D_*ori ≠ D_*(-ori)` of that subspace; `A` states this for `OrTangent`s of `X.PObj`, which do
  not express `B`'s frames.  `B`'s hypotheses include Property (T) for both structures (as the
  text); `A`'s `proposition_9_4_10` does not need it (its pieces are cut out by the finitely many
  values of `y ↦ (I_y, I'_y, J₊(y), J'₊(y))`), so `A`'s hypotheses are not the obstacle.
* `B → A` fails.  `A` holds for every ep-groupoid and every `SheetGeometry`; `B` covers one
  concrete model.  `A` also contains `tangent_eq_iff_of_mem_ess` (under (T), the sign map on
  `K(i, i')^e` is constant), not a statement of `B`, and the Example 9.3.5 witnesses (on the graph
  sheets in `ℝ²` with `graphSheetGeometry`: `♯P₀ = 2`, the hypotheses (a), (b) for the two
  decompositions, `M_U = M'_U`), closed facts about specific objects that `B` does not mention.
-/

namespace RoundTrip.V9_48
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.proposition_9_4_10.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.tangent_eq_iff_of_mem_ess.{0}) ∧
  (type_of% @Polyfold.example935_two_le_numClasses) ∧
  (type_of% @Polyfold.example935_hypotheses_9_4_10) ∧
  (type_of% @Polyfold.example935_MU_eq)

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.proposition_9_4_10.{0}, @Polyfold.EpGroupoid.tangent_eq_iff_of_mem_ess.{0},
    @Polyfold.example935_two_le_numClasses, @Polyfold.example935_hypotheses_9_4_10,
    @Polyfold.example935_MU_eq⟩

end RoundTrip.V9_48
