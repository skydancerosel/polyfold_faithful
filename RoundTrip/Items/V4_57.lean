import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_57

/-! Round trip for V4_57 (proof of Theorem 4.23: the strata `A ∩ F_σ°`, their dimension, Sard on
the strata).

`A` is the conjunction of the types of the two theorems of the item, `Polyfold.finrank_stratSub`
and `Polyfold.measure_image_stratCritSet` (no universe parameters: `V`, `F : Type`); the
definitions `quadC`, `stratSub`, `zeroSetOf`, `stratCritSet` are their vocabulary.

Neither direction is proved; the two sides live on different levels.

* `A` is the **finite-dimensional model** of the step: for a finite-dimensional `V` with linear
  coordinates `ℓ : V → ℝⁿ` (onto), `dim stratSub ℓ σ + #σ = dim V` (the dimension count), and for
  `f` of class `C^∞` on `O ∩ {ℓ ≥ 0}`, the image of the stratified critical set
  `{v | Df(v)|_{stratSub ℓ σ(v)} not onto}` is null for every Haar measure (Sard on the strata).
* `B` is the **M-polyfold statement**: for the data of Theorem 4.23 and `z ∈ A`, a neighbourhood
  `U` with exactly `d_Z(z)` local faces (Theorem 4.22 (1)), each `A ∩ F_σ°` a smooth submanifold
  whose induced structure has no boundary, `dim T_{z'}A = k + #σ`, `dim T_{z'}(A ∩ F_σ°) = k` in
  every chart, and full measure of the regular values of every `p_σ` and of their intersection.

`A → B` fails: from the model lemmas one would still need Theorem 4.22 (the local faces of `U`,
the identification of `A ∩ F_σ°` in a tame chart with the open stratum of the graph domain, its
sc⁺-retractions and the boundaryless induced structure), the transport of tangent-space
dimensions to every chart, and the translation of the model's stratified critical values into
B's `regValues` (regularity of `p_σ` read on `T(A ∩ F_σ°)` instead of `Df|_{stratSub}`); that is
the bulk of `exists_local_family` plus face theory the project does not state in this form,
i.e. substantial mathematics, not glue.  `B → A` fails: `B` only speaks of submanifolds of
`ℝᵐ × X` for tame `X` under the global hypotheses of Theorem 4.23 (compact closure, compact
nonempty fibres for `|λ| ≤ ε`); it says nothing about an arbitrary `C^∞` map `f : V → F` into an
arbitrary finite-dimensional `F` with an arbitrary Haar measure, nor about the linear algebra of
`stratSub` (which holds outright).  Realizing `A`'s data as such a submanifold would require
building M-polyfolds from `(V, ℓ, O)` and satisfying (1). -/

namespace RoundTrip.V4_57
open Polyfold

/-- The project's statement (no universe parameters). -/
def A : Prop :=
  (type_of% @Polyfold.finrank_stratSub) ∧ (type_of% @Polyfold.measure_image_stratCritSet)

theorem A_holds : A := ⟨@Polyfold.finrank_stratSub, @Polyfold.measure_image_stratCritSet⟩

end RoundTrip.V4_57
