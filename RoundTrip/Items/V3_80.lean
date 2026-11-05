import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_80

/-!
Round trip for V3_80 (Theorem 3.54, property (4) in the chart at `x₀`; Corollary 3.41 and
Lemma 3.55).  `A` is the conjunction of the types of `Polyfold.theorem_3_54_nearby` (universes
`u, v` instantiated at `0`), `Polyfold.lemma_3_55_relOpen` and
`Polyfold.StabilityData.exists_surjective_Dfs'_graph` (no universe parameters);
`Polyfold.coordCLMWith` is vocabulary.  Since the germ reading (refresh 2026-11-02)
`theorem_3_54_nearby` assumes the text's germ reading (`IsGoodPositionGermTame`: filling germ,
sc⁺-germ); `B`'s whole-chart `IsGoodPosData` (`IsFilledVersion`, `IsScSmooth c.U s`) implies it, so
the hypotheses still match and the gaps below are unchanged.

Neither direction is proved; both gaps are genuine (not proof effort only).

* `A → B`:
  - **Quantifier over the data.**  B's claim is made for *every* good-position datum
    `(c, g, s, D)` at `x₀` handed to it (the chart `c` centred at `x₀`, the filled version `g`, the
    sc⁺-section `s`, the conjugation `D` of `g − s`).  `theorem_3_54_nearby` is existential: it
    produces its own chart `c`, its own coordinate change `ψ`, data `𝒮` of Theorem 3.38 and its own
    `σ`, so it says nothing about B's `c` and `D`.
  - **What is concluded at the nearby zeros.**  B's `SurjGoodPosInChart c f y` is about the
    linearization in the chart `c` at `z = φ(y)`: `L = D(f̂ ∘ r)(z)` maps `T_zO` onto `K_z`, and
    `ker L ∩ T_zO` is in good position (with an *sc*-complement, `IsInGoodPositionScIn`) to
    `T_zO ∩ C_z`.  A states, in the coordinates `ψ ∘ φ` it chose, that `D(h + t)(z)` is surjective
    Fredholm and that the graph tangent space `N_v = {n + Dσ(v)n}` is in good position to `C'_z`
    with the algebraic, closed good complement `Yc`; the identification `N_v = ker D(h + t)(z)` and
    the passage back to the chart `c` (`T_zO`, `K_z`, chart independence) are explicitly not in A
    (they are `graphSpace_eq_ker_Dfs'`, `theorem_3_54_nearby_kernel`, `LinearizationCharts.lean`).
  - **Regularity of `σ`** (B's `GraphFormCor` uses `IsGraphSolution`): B wants `σ : K → E'₁` of
    class `C¹` into level `1` on `V'` and an sc-smooth germ (one germ of neighbourhoods) into `E'¹`;
    A has `σ` into level `0`, `C¹` there, with values on level `1` and (via the cited
    `theorem_3_47`) `C^k`-lifts on `k`-dependent neighbourhoods.
  - Hypotheses do match in the easy direction (B's `IsScFredholmSectionTame`, tame bundle and
    `IsGoodPosData` with an sc-complement give the project's `IsGoodPositionGermTame`, through
    `IsGoodPositionGermTameWholeChart`, cf. V3_70/V3_84), so the failure is in the conclusion.
* `B → A`: `lemma_3_55_relOpen` (any finite-dimensional `N` in good position to any presented
  partial quadrant, any `C¹` `σ`) and `exists_surjective_Dfs'_graph` (any `StabilityData`, any
  basic germ) are general lemmas not about solution sets of sections, and `theorem_3_54_nearby`
  needs only `IsSection` and `IsGoodPositionGermTame` (no sc-Fredholm property, no tame bundle
  atlas), so B, with its stronger hypotheses, cannot give them.
-/

namespace RoundTrip.V3_80
open Polyfold

/-- The project's statement: the listed theorems, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.theorem_3_54_nearby.{0, 0} ∧ type_of% @Polyfold.lemma_3_55_relOpen ∧
    type_of% @Polyfold.StabilityData.exists_surjective_Dfs'_graph

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_54_nearby.{0, 0}, @Polyfold.lemma_3_55_relOpen,
    @Polyfold.StabilityData.exists_surjective_Dfs'_graph⟩

end RoundTrip.V3_80
