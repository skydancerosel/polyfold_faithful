import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_106

/-!
Round trip for V3_106 (Theorem 3.18 for tame germ data).  `A` is the conjunction of the types of
`Polyfold.theorem_3_1_21_tame`, `Polyfold.PullbackChartData.ofProd_isTame`,
`Polyfold.StrongBundle.IsScFredholmGermTame.param` and
`Polyfold.StrongBundle.IsScFredholmSectionTame.param`, universes instantiated at `0`.

Refresh 2026-11-02: `theorem_3_1_21_tame`, `IsScFredholmGermTame.param` and
`IsScFredholmSectionTame.param` now state the germ reading of Definitions 3.50/3.51 (filling and
sc⁺-section as germs, in a tame chart), and so does B's `IsScFredholmSectionTame`; the proof is
unchanged.

* `A → B`: B is `theorem_3_1_21_tame` with the extra hypothesis `IsTameStrongBundle Bd` (unused);
  the instance arguments, the proof `hπ` and the section proofs `hf`, `hs` agree with the
  project's by proof irrelevance.
* `B → A` is not proved: `A` assumes no tame strong bundle, and its other conjuncts are chart- and
  germ-level statements (the product chart of a tame chart is tame; tame germ data of
  `f̃ = f ∘ π` at a single point) that `B` does not state.
-/

namespace RoundTrip.V3_106
open Polyfold

/-- The project's statement: Theorem 3.18 for tame germ data and its three lemmas, universes at
`0`. -/
def A : Prop :=
  type_of% @Polyfold.theorem_3_1_21_tame.{0, 0} ∧
    type_of% @Polyfold.PullbackChartData.ofProd_isTame.{0, 0} ∧
    type_of% @Polyfold.StrongBundle.IsScFredholmGermTame.param.{0, 0} ∧
    type_of% @Polyfold.StrongBundle.IsScFredholmSectionTame.param.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_1_21_tame.{0, 0}, @Polyfold.PullbackChartData.ofProd_isTame.{0, 0},
    @Polyfold.StrongBundle.IsScFredholmGermTame.param.{0, 0},
    @Polyfold.StrongBundle.IsScFredholmSectionTame.param.{0, 0}⟩

theorem A_to_B : A → B := by
  intro hA X _ _ _ PX Y _ _ _ P _ _ Bd n f s _ _ hπ hf hs _ hfF hsP
  exact hA.1 hfF hsP

#rt_check RoundTrip.V3_106.A_to_B [Polyfold.theorem_3_1_21_tame,
  Polyfold.PullbackChartData.ofProd_isTame, Polyfold.StrongBundle.IsScFredholmGermTame.param,
  Polyfold.StrongBundle.IsScFredholmSectionTame.param]

end RoundTrip.V3_106
