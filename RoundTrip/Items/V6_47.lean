import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_47

/-! Round trip for V6_47 (Lemma 6.34: the convex homotopy of the sections `s`).

A is the type of `IsStabKernels.push_square` (universes at `0`; `sqEdge`, `sqPath` are
definitions): for stabilized kernels `hΛ` over a simply connected, locally path-connected
parameter space `Q` and paths `γ₀ : a ⇝ a'`, `γ₁ : b ⇝ b'` along which the points stay at `x₀`,
`x₁` and the end-point operators `(f + S_q)'(xᵢ)` and the values `ŝᵢ(q)(xᵢ)` vary continuously,
the **signed** push-forwards from `a` to `b` and from `a'` to `b'` agree.

**No direction is proved.**

* B (1) is about B's unsigned `Facts.push` (the text's `φ_*` read literally,
  `orEquivRay⁻¹ ∘ propagate ∘ orEquivRay`), A about `IsStabKernels.push`, which inserts
  `α(T) = stabSign T = (−1)^{dim coker T}` at both end points.  For the same data they differ by
  `α(T^τ₀) α(T^τ₁)`, and along the convex homotopy `T^τ_t = (f − s^τ(·, t))'(φ(t))` moves, so
  `dim coker` at an end point can jump.
* B (1) does not hold as we read it (not formalized here).  Take `X = ℝ` (`rnPolyfold 1`), the
  trivial bundle `ℝ × ℝ → ℝ` (`TrivialBundle.bundle 1 1`), `f = 0` (sc-Fredholm), `φ ≡ 0`,
  `s⁰ = 0`, `s¹(y, t) = t·y` (both through `f(φ(t)) = 0`), `k = 1`, `σ₁ ≡ 1` over the square.  Then
  `F^τ_t(λ, y) = −τ t y + λ` has onto linearization for every `(τ, t)` and there is no boundary,
  so (P) holds for every `τ`.  The signed push-forward is the same for all `τ` (A; directly, by
  `cont_orRay_path`, since the point is fixed), `T^τ₀ = 0` (coker `1`) for all `τ`, and
  `T^τ₁ = −τ` (coker `1` at `τ = 0`, `0` at `τ = 1`).  So `α α = +1` at `τ = 0` and `−1` at
  `τ = 1`: `(F 1).push = −(F 0).push ≠ (F 0).push`.  The linear-algebra core is the project's
  `not_isLineOrientation_stabRay_uncorrected`.  A formal `not_B` needs the full instance and was
  not attempted within the budget.
* So `A ⇒ B` is false.  Even with the sign repaired, `A ⇒ B (1)` would not be glue: `push_square`
  needs one family of stabilized kernels over the square `[0, 1]²` (continuous in `(τ, t)`
  jointly), while B provides a separate `Facts` (a kernel family over `t ∈ [0, 1]`) for each `τ`
  and only the slice-wise (P); producing the joint family is the content of the text's proof
  (Lemma 6.30 over the square).  B (2)–(3) (`T^τ_{0,1} ∈ Lin`, continuity in `τ`) are not in A at
  all; they follow from `Facts.lin0/lin1` and the affine dependence `linAt_principal_combo`.
* `B ⇒ A` holds only vacuously (B is false); it is not proved, and A is far more general
  (any parameter space, any deformation with fixed end points).
-/

namespace RoundTrip.V6_47
open Polyfold

/-- The project's statement: the theorem of the item, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.IsStabKernels.push_square.{0, 0, 0}

theorem A_holds : A := @Polyfold.IsStabKernels.push_square.{0, 0, 0}

end RoundTrip.V6_47
