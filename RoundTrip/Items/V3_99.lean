import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_99

/-!
Round trip for V3_99 (Theorem 3.19: `ker f'(y) = T_yS(f, U)`), refreshed 2026-11-02 against HEAD
(germ reading).  `A` is the conjunction of the types of `theorem_3_54_ker_eq_tangent`,
`theorem_3_54_nearby_kernel` and `linAt_eq_germDeriv` (which replaced `linAt_eq_scDeriv` in the
row), universes instantiated at `0` (`linAt_eq_germDeriv` has none).

Neither direction is proved; both gaps are genuine.

* `A → B`.  (i) Hypotheses: `B` assumes `d_X ≡ 0`, an `IsScFredholmSection` (germ data in some
  compatible chart, no tameness) and `IsLinSurjAt` at `x₀`; `A`'s `theorem_3_54_ker_eq_tangent` and
  `theorem_3_54_nearby_kernel` need `(f, x₀)` in good position **in a tame chart**
  (`IsGoodPositionGermTame`, germ reading), and the project has no lemma producing tame germ data
  from `B`'s hypotheses (the same gap as V3_68; the project's route is
  `isGoodPositionGerm_of_isLinSurjAt`, which needs `IsScFredholmSectionTame`).  (ii) Conclusions:
  `B` asserts that `S(f, U)` is a sub-M-polyfold, that `f'(y)` is onto in **every** chart at every
  `y ∈ S(f, U)`, and that the intrinsic tangent space `T_yS` of the induced M-polyfold, pushed into
  a chart of `X` by the tangent map of the inclusion (`tangentMap`, `tangentChartMap`), is
  `ker D(f̂ ∘ r)(z) ∩ T_zO` in every chart.  `A` does not give the sub-M-polyfold, gives
  surjectivity of `Dg(z₀)` only in its own chart, and its kernel statement is the identity
  `Dψ(z)(ker Lin(z)) = graph(Dσ(v))` in one specific chart `ψ ∘ φ` (the tangent space of the
  solution **graph**), not a statement about `TangentSpace` of `subPolyfold`; linking the two needs
  the tangent bundle of the induced structure and its chart maps, which is new work.
* `B → A`.  `A` has no `d_X ≡ 0` hypothesis and no surjectivity hypothesis beyond good position,
  exhibits explicit chart data (the conjugating sc-diffeomorphism `ψ`, the solution graph `σ`,
  the filling germ and the basic germ), and contains the general local lemma `linAt_eq_germDeriv`
  (on `T_zO`, `Lin(z) = Dg(z)` for any germ `g` with derivative family `Dg` agreeing with `f̂` on
  `O` near `z`), none of which `B` states.
-/

namespace RoundTrip.V3_99
open Polyfold

/-- The project's statement, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.theorem_3_54_ker_eq_tangent.{0, 0} ∧
    type_of% @Polyfold.theorem_3_54_nearby_kernel.{0, 0} ∧
    type_of% @Polyfold.linAt_eq_germDeriv

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_54_ker_eq_tangent.{0, 0}, @Polyfold.theorem_3_54_nearby_kernel.{0, 0},
    @Polyfold.linAt_eq_germDeriv⟩

end RoundTrip.V3_99
