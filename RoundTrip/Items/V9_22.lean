import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_22

/-! Round trip for V9_22 (Proposition 9.2.8 and Lemmas 9.2.9–9.2.11, pp. 413–417 of the 2021
book; 2017: Proposition 9.3, Lemmas 9.6–9.8): the graph representation and tangent slices.

`A` is the conjunction of the types of the ten listed theorems, universes instantiated at `0`
(`B` lives in `Type`); the six listed definitions (`HasTangentSlicesAt`, `IsGraphChartAt`,
`HasGraphChartsAt`, `HasGraphChartAt`, `IsGraphBallAt`, `HasGraphBallAt`) are vocabulary:
* conditional results: `hasTangentSlicesAt_of_hasGraphChartsAt` (graph representation in one
  chart ⇒ tangent slices, the slice form of Proposition 9.2.8),
  `exists_slice_of_isGraphChartAt`, `exists_generic_slice` (slices for mixed-dimensional
  families, avoiding lower-dimensional sets), `hasOrientedGoodPointsAt_of_hasGraphBallAt`
  (graph representation over a ball + continuous level-1 coordinates ⇒ good points `y_e` in
  every neighbourhood, one per block, with orientations);
* the `ℝᵐ` instances `isGraphChartAt_rn`, `hasGraphChartsAt_rn`, `hasTangentSlicesAt_rn`,
  `hasGraphChartAt_rn`, `hasGraphBallAt_rn`;
* the inverse-function lemma `exists_mem_graph_of_hasStrictFDerivAt` (on a normed space).

Neither direction is proved; this file only records `A`.

* `A → B` fails for a genuine reason, not only effort.  (i) Every general-M-polyfold conjunct of
  `A` is conditional on a graph-representation hypothesis (`HasGraphChartsAt`, `HasGraphChartAt`,
  `HasGraphBallAt`, plus `HasContinuousLevelOneOn`) that the project proves only in `ℝᵐ`;
  `B` asserts the conclusions in every M-polyfold with no such hypothesis.  (ii) Even where the
  hypotheses hold, `A`'s conclusions are not `B`'s: `A` gives, for each open `W ∋ x`, one slice
  `F` or one family of points `y_e` with a partition that may depend on `W`, whereas `B`'s
  Proposition 9.2.8 asks for ONE partition `Ξ = ⊔ I^e` and sequences `x^e_k → x` of good points of
  `Θ` (a pigeonhole over the finitely many partitions would be needed, and
  `hasOrientedGoodPointsAt_of_hasGraphBallAt` also needs orientations of the `Mᵢ`).  (iii) `B`'s
  Lemmas 9.2.9–9.2.11 are statements about EVERY chart `φ` with `φ(x) = 0` and the actual
  partial quadrant `C` (interior of `L ∩ C` in `L`; graphs over a cone around every interior
  `h₀ ≠ 0`, for every projection; a `C¹` parametrization `Γ` of `Mⱼ` over `L ∩ C` with `Pr ∘ Γ`
  injective with invertible derivative), whereas `IsGraphChartAt` is about ONE chart and an
  abstract set `K` of admissible directions, with an `ε`-approximate (not exact, not unique)
  graph property and no parametrization `Γ`.
* `B → A` fails: `A` contains the `ℝᵐ` instances (the inverse function theorem applied to
  retractions of `ℝᵐ`), the normed-space lemma `exists_mem_graph_of_hasStrictFDerivAt` and the
  slice lemmas for mixed-dimensional families, none of which `B` (about the sheets of a branched
  ep⁺-subgroupoid at a bad point) states or implies. -/

namespace RoundTrip.V9_22
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.MPolyfold.hasTangentSlicesAt_of_hasGraphChartsAt.{0}) ∧
  (type_of% @Polyfold.exists_mem_graph_of_hasStrictFDerivAt.{0}) ∧
  (type_of% @Polyfold.MPolyfold.isGraphChartAt_rn) ∧
  (type_of% @Polyfold.MPolyfold.hasGraphChartsAt_rn) ∧
  (type_of% @Polyfold.MPolyfold.hasTangentSlicesAt_rn) ∧
  (type_of% @Polyfold.MPolyfold.hasGraphChartAt_rn) ∧
  (type_of% @Polyfold.MPolyfold.exists_slice_of_isGraphChartAt.{0, 0}) ∧
  (type_of% @Polyfold.MPolyfold.exists_generic_slice.{0, 0, 0}) ∧
  (type_of% @Polyfold.hasGraphBallAt_rn) ∧
  (type_of% @Polyfold.MPolyfold.hasOrientedGoodPointsAt_of_hasGraphBallAt.{0})

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.hasTangentSlicesAt_of_hasGraphChartsAt.{0},
    @Polyfold.exists_mem_graph_of_hasStrictFDerivAt.{0},
    @Polyfold.MPolyfold.isGraphChartAt_rn, @Polyfold.MPolyfold.hasGraphChartsAt_rn,
    @Polyfold.MPolyfold.hasTangentSlicesAt_rn, @Polyfold.MPolyfold.hasGraphChartAt_rn,
    @Polyfold.MPolyfold.exists_slice_of_isGraphChartAt.{0, 0},
    @Polyfold.MPolyfold.exists_generic_slice.{0, 0, 0}, @Polyfold.hasGraphBallAt_rn,
    @Polyfold.MPolyfold.hasOrientedGoodPointsAt_of_hasGraphBallAt.{0}⟩

end RoundTrip.V9_22
