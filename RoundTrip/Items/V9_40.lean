import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_40

/-! Round trip for V9_40 (Lemma 9.4.2, 2021 p. 430; 2017: Lemma 9.11: the essential set is closed).

`A` is the conjunction of the types of `lemma_9_4_2` (`K^e` closed in the subspace `K`) and
`lemma_9_4_2_open` (`K ∖ K^e` open in `K`), universes at `0`: for every model with corners
`I : H → E` (any real normed space `E`), every charted space `M` over `H` (no smoothness
assumed) and every `K ⊆ M`, about the project's `essentialSet I K`.

`B` is the same pair of claims, about the same `essentialSet`, for an `n`-dimensional smooth
manifold with corners modelled on the quadrant `[0, ∞)ⁿ ⊆ ℝⁿ` (`modelWithCornersEuclideanQuadrant
n`, `IsManifold _ ∞ M`).

* `A ⇒ B` (`A_to_B`): specialize `A` to `I = modelWithCornersEuclideanQuadrant n`.
* `B ⇒ A` fails: `B` speaks only of quadrant models of finite dimension and of `C^∞` manifolds;
  `A` is the statement for every model with corners (e.g. `𝓘(ℝ, E)` for an infinite-dimensional
  `E`, or `Fin 2 → ℝ` with its sup norm) and every charted space, which no instance of `B`
  covers.  The difference is generality only: on the quadrant models `A` and `B` say the same.
-/

namespace RoundTrip.V9_40
open Polyfold

/-- The project's statements, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.lemma_9_4_2.{0, 0, 0} ∧
  type_of% @Polyfold.lemma_9_4_2_open.{0, 0, 0}

theorem A_holds : A := ⟨@Polyfold.lemma_9_4_2, @Polyfold.lemma_9_4_2_open⟩

theorem A_to_B : A → B := by
  rintro ⟨h1, h2⟩ n M _ _ _ K
  exact ⟨h1 K, h2 K⟩

#rt_check RoundTrip.V9_40.A_to_B [Polyfold.lemma_9_4_2, Polyfold.lemma_9_4_2_open]
#rt_overlap RoundTrip.V9_40.A_to_B [Polyfold.lemma_9_4_2, Polyfold.lemma_9_4_2_open]

end RoundTrip.V9_40
