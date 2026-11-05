import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_62

/-! Round trip for V4_62 (proof of Theorem 4.23: general position of the fibre `A_λ`).

`A` is the type of `Polyfold.isGeneralPositionRetractAt_slice` (no universe parameters).

Neither direction is proved.

* `A` is a **chart lemma**: for a retraction `t` onto the chart model of `A ⊆ ℝᵐ ⊕ E` inside the
  product retract `id × r` (`r` tame for the presentation `T_X`), general position of `t` at `z`,
  stratified regularity at `z` (`v ↦ v.1` maps `T_z t ∩ E_z` onto `ℝᵐ`), and an sc⁺-retraction
  `τ ⊆ r` through `z.2` **whose tangent space contains `{a.2 | a ∈ T_z t, a.1 = 0}`** (`hTQ`),
  `τ` is in general position at `z.2`.
* `B` is the **M-polyfold statement** under the hypotheses of Theorem 4.23, in an ARBITRARY
  (not necessarily tame) product chart, with sc⁺-data `(V', s')` for the fibre `A_λ` near `x'`:
  (a) the decomposition `T_{z'}A ∩ (ℝᵐ × E) = ({0} × (T_{x'}A_λ ∩ E)) ⊕ ξ` with `ξ ≅ ℝᵐ`, and
  (b) `A_λ` is in general position at `x'` (Definition 4.21).

`A → B` fails for a genuine reason: B does not assume `hTQ`; it only knows that the image of
`s'` is the fibre `A_λ`.  The inclusion `ker(Tp|T_{z'}A) ⊆ T_{x'}A_λ` (equivalently, for (a),
`T_{x'}A_λ ∩ E = {w ∈ E | (0, w) ∈ T_{z'}A}`) is the content of the implicit function theorem
in partial quadrants for `p|_A` at the corner point `z'` (in the project:
`exists_fibre_retraction`, `exists_slice_retraction`, and the dimension count), i.e. real
mathematics.  Moreover (a) is not in `A` at all, `B`'s chart is arbitrary while `A` needs `r`
tame (a chart change of the regularity hypothesis would be needed), and B's chart data
(`SubmanifoldData`, `exists_chartRetraction`) must be turned into `A`'s retractions.
`B → A` fails: `A` holds for arbitrary retractions `t`, `τ` of an arbitrary sc-Banach model with
the hypothesis `hTQ`, without any of B's global hypotheses (compact closure, (1), tameness of
`A`); `B` cannot be instantiated at such chart data without constructing an M-polyfold and a
submanifold realizing them. -/

namespace RoundTrip.V4_62
open Polyfold

/-- The project's statement (no universe parameters). -/
def A : Prop := type_of% @Polyfold.isGeneralPositionRetractAt_slice

theorem A_holds : A := @Polyfold.isGeneralPositionRetractAt_slice

end RoundTrip.V4_62
