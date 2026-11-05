import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_63

/-! Round trip for V4_63 (the local step of Theorem 4.23).

`A` is the type of `Polyfold.exists_local_family`, universe `0` (`FibreLocal` is its vocabulary).

Neither direction is proved.

* `A`: for `X` tame and `A ⊆ ℝᵐ × X` a smooth submanifold in general position at every point
  (no other hypothesis), every `z₀ ∈ A` has an open `U ∋ z₀` and a null set `CV ⊆ ℝᵐ` such that at
  every `z ∈ A ∩ U` with `z.1 ∉ CV`: `z` is a stratified regular point (`Tp` maps `T_zA ∩ E_z` onto
  `ℝᵐ`), `A_{z.1}` is near `z.2` the image of an sc⁺-retraction, and `A_{z.1}` is in general and
  in good position at `z.2` (`FibreLocal`).
* `B`: under ALL hypotheses of Theorem 4.23, every `z ∈ A` has an open `U ∋ z` with exactly
  `d_Z(z)` local faces `F_i` (Theorem 4.22 (1)), the common regular values of the restrictions
  `p_σ` to the open strata `A ∩ F_σ°` have full measure, and over each of them
  `(A ∩ U)_λ` is a smooth submanifold of `X` in general position at each of its points.

`A → B` fails for genuine reasons: `A`'s `U` carries no face structure (B's `IsLocalFacesB`
needs Theorem 4.22 (1)); B's regular values are those of the `p_σ` on the strata `A ∩ F_σ°`,
read through sc⁺-data for each stratum (`IsRegularPointOnB`), and passing from `A`'s stratified
regularity (`T_zA ∩ E_z`) to them needs the strata to be submanifolds with
`T_{z'}(A ∩ F_σ°) = T_{z'}A ∩ E_{z'}` (Theorem 4.22 (4)) — real mathematics.  (The fibre part
would be glue: shrinking `A`'s local sc⁺-retraction to `{x | (λ, x) ∈ U}` and
`IsGeneralPositionAt.congr_nhds`.)
`B → A` fails for genuine reasons: B assumes compact closure of `A`, compact NONEMPTY fibres for
`|λ| ≤ ε`, and tameness of the induced structure on `A`, none of which `A` assumes, and (1)
cannot be arranged by localizing at a critical point of `p`; in the other direction B does not
give `A`'s stratified regularity (`T_zA ∩ E_z` onto) from the regularity of `p_σ` on
`T(A ∩ F_σ°)` without the same identification of the strata's tangent spaces, nor the good
position of the fibre, nor sc⁺-data for `A_λ` itself (only for `(A ∩ U)_λ`). -/

namespace RoundTrip.V4_63
open Polyfold

/-- The project's statement, universe `0`. -/
def A : Prop := type_of% @Polyfold.exists_local_family.{0}

theorem A_holds : A := @Polyfold.exists_local_family.{0}

end RoundTrip.V4_63
