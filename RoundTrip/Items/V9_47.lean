import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_47

/-! Round trip for V9_47 (Proposition 9.4.9, 2021 p. 434; 2017: Proposition 9.5): the
decomposition `M_U^* = ⨆_J M_U^J` and the form of `Θ`, `TΘ`, `T̂Θ` on `M_U^J`.

`A` is the conjunction of the types of the two listed theorems, universes instantiated at `0`
(`B` lives in `Type`): `EpGroupoid.LocalBranchingStructure.tangentValue_eq_sum` and
`EpGroupoid.proposition_9_4_9`.  `MPolyfold.SheetGeometry.MStarPart` is a definition
(vocabulary).

Neither direction is proved; the difference is genuine.

* The settings differ.  `A` is about an oriented local branching structure `B` of a branched
  ep⁺-subgroupoid `Θ` on an ep-groupoid `X`, with an abstract `SheetGeometry` `G` on `X.PObj`
  (essential points and null sets as data, Lemmas 9.4.4 and 9.4.6 and the tangent note as fields),
  tangent spaces `X.PObj.submanifoldTangent` and oriented tangents `OrTangent` in Part I's tangent
  bundle, `TΘ = X.tangentValue Θ` (Theorem 9.2.1, under `HasIndependentTangentSums`).  `B` is
  about the local model: sheets `jᵢ : Nᵢ → F` immersed `n`-manifolds with corners in a Banach
  space, `T_yMᵢ = Djᵢ(ℝⁿ)`, orientations `oᵢ(w)` of `ℝⁿ` pushed to frame sets in `F`
  (`posFramesB`), `TΘ`, `T̂Θ` defined as formal sums.  The project has no M-polyfold /
  ep-groupoid structure on `F` whose tangent objects are `B`'s.
* `A → B` fails.  (a) `A` assumes Property (T) on `U(x)` (`hT`); `B` does not (its `a, b` may
  depend on `y`), and `B`'s hypotheses do not give (T) (it is satisfiable after shrinking `U(x)`,
  Lemma 9.4.3, not formalized).  (b) `B`'s (2)–(4) need, on `M_U^J`, `T_yMⱼ = T_yMⱼ'` in `F` for
  `j, j' ∈ J` (Lemma 9.4.4 and the tangent note for `B`'s sheets, along the chains of
  `∼_y`), and that the oriented tangents of the sheets of `J` are the two orientations
  `D_*ori`, `D_*(-ori)` of one subspace of `F`; `A` takes the first as `SheetGeometry` fields
  and states the second for `OrTangent`s of `X.PObj`, which do not express `B`'s frames.
  (The null-set and decomposition parts of `B` are combinatorial: for Lemma 9.4.8 they follow
  from the abstract statement through a tagged discrete `SheetGeometry`, V9_46; here `A` would
  also need an ep-groupoid with an oriented branching structure, (T) and independent tangent sums
  built around it.)
* `B → A` fails.  `A` holds for every ep-groupoid and every `SheetGeometry`, with `A_J` constant
  on `M_U^J` (from (T)); `B` covers one concrete model and has `y`-dependent `a, b`.  `A`'s
  `tangentValue_eq_sum` (`TΘ(y) = ∑_{I_y} σᵢ T_yMᵢ` from Theorem 9.2.1's independence) is part of
  `B`'s definition of `TΘ`, not a statement of `B`.
-/

namespace RoundTrip.V9_47
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.tangentValue_eq_sum.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.proposition_9_4_9.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.LocalBranchingStructure.tangentValue_eq_sum.{0},
    @Polyfold.EpGroupoid.proposition_9_4_9.{0}⟩

end RoundTrip.V9_47
