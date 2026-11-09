import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_48

/-!
Round trip for V3_48 (Theorem 3.54, claim (3) of its proof).  `A` is the conjunction of the types
of `Polyfold.theorem_3_6_8_graph`, `Polyfold.theorem_3_6_8_linear`,
`Polyfold.theorem_3_6_8_linear_of_isTameWith`, `Polyfold.IsInGoodPositionIn.isInGoodPosition`,
`Polyfold.scDeriv_mem_iff_of_inverse`, `Polyfold.IsStrongBundleIso.pushforward_linearization`,
`Polyfold.theorem_3_6_8_pushforward` and `Polyfold.scDeriv_eq_of_eqOn_nhds`, universes
instantiated at `0`.  Since the germ reading (refresh 2026-11-02) `theorem_3_6_8_graph` and the
lemmas about good position assume the text's germ reading (`IsGoodPositionGermTame`: filling germ,
sc⁺-germ); the statements are otherwise as in the audit.

Neither direction is proved; both gaps are genuine, and neither is about the whole-chart reading.

* `A → B`:
  - B's graph claim (3) is stated for **every** good-position datum `(c, g, s, D)` at `x` (the
    given chart centred at `x`, filled version `g`, sc⁺-section `s`, conjugation `D` of `g − s`):
    `ψφ(S) = {v + σ(v) | v ∈ V'}` with `ψ = base D.Ψ` and `K = ker D(D.Ψ_* g)(0)`.  A's
    `theorem_3_6_8_graph` gives the graph description only for **some** chart `c` and **some**
    conjugation `ψ` that it chooses itself (an existential), so it says nothing about the data B
    is handed; transferring it to arbitrary data would mean re-proving the local solution theorem
    in that chart.
  - B's claims (1) (good position, with an *sc*-complement, at every zero of `V`) and (2) (`S` is a
    sub-M-polyfold with a corner structure) are not in A at all: the listed theorems are part (3)
    and linear-algebra lemmas of the proof (`theorem_3_6_8_linear(_of_isTameWith)`,
    `theorem_3_6_8_pushforward`, `pushforward_linearization`, the transport lemma
    `IsInGoodPositionIn.isInGoodPosition`, `scDeriv_mem_iff_of_inverse`,
    `scDeriv_eq_of_eqOn_nhds`).  Moreover A's good position uses an algebraic complement
    (`IsGoodPositionGermTame`, `IsGoodComplement`), B's an sc-complement (`IsGoodComplementSc`).
  - At HEAD `B`'s claim (1) uses the blind file's whole-chart `IsGoodPositionGermSc`
    (`IsFilledVersion`, `IsScSmooth c.U s`) at the nearby zeros, while its sc-Fredholm hypothesis is
    the germ reading: (1) is now stronger than the text's (whole-chart data at the nearby zeros do
    not follow from germ data, Findings item 260).
* `B → A`: A's general lemmas (derivatives of conjugated maps, the transport of good position, the
  linearization of a push-forward, uniqueness of derivatives on quadrant-like sets) are not
  statements about solution sets and do not follow from B; and A's graph theorem asserts more
  about `σ` (`C¹`, `σ(0) = 0`, `Dσ(0) = 0`, values on level `1`, `C^k` lifts, closed complement,
  smooth kernel, injectivity of `ψ ∘ φ` on `Vx`) than B's `GraphForm`, under weaker hypotheses
  (any strong bundle, `IsSection`, no tame bundle atlas).
-/

namespace RoundTrip.V3_48
open Polyfold

/-- The project's statement: the theorems listed for Theorem 3.54 (3), universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.theorem_3_6_8_graph.{0, 0} ∧ type_of% @Polyfold.theorem_3_6_8_linear ∧
    type_of% @Polyfold.theorem_3_6_8_linear_of_isTameWith ∧
    type_of% @Polyfold.IsInGoodPositionIn.isInGoodPosition ∧
    type_of% @Polyfold.scDeriv_mem_iff_of_inverse ∧
    type_of% @Polyfold.IsStrongBundleIso.pushforward_linearization ∧
    type_of% @Polyfold.theorem_3_6_8_pushforward ∧ type_of% @Polyfold.scDeriv_eq_of_eqOn_nhds

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_6_8_graph.{0, 0}, @Polyfold.theorem_3_6_8_linear,
    @Polyfold.theorem_3_6_8_linear_of_isTameWith, @Polyfold.IsInGoodPositionIn.isInGoodPosition,
    @Polyfold.scDeriv_mem_iff_of_inverse, @Polyfold.IsStrongBundleIso.pushforward_linearization,
    @Polyfold.theorem_3_6_8_pushforward, @Polyfold.scDeriv_eq_of_eqOn_nhds⟩

end RoundTrip.V3_48
