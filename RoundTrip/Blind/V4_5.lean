import Polyfold
/-! Blind formalization of V4_5 (the text's §4.1, Theorem 4.2, p. 147).

Text: for a tame M-polyfold `X` the following are equivalent.  (i) `X` has a compatible smooth
manifold structure with boundary with corners.  (ii) `X_0 = X_∞` and `1_0^1 : X → X^1` is
sc-smooth; every `x` lies in a tame chart `(V, ψ, (O, C, E))` with `ψ(x) = 0` whose tangent space
`T_0O` is finite-dimensional and in good position to `C`.

Choices:
- Setting: `X : Type` (universe 0, as asked), Hausdorff paracompact, `P : MPolyfold X`, assumed
  tame (`P.IsTame`, Definition 2.37, checked with `#print`: an equivalent atlas of charts on tame
  retracts).  B is `P.IsTame → ((i) ↔ (ii))`.
- (i): the project's `P.HasCornerStructure` (Definition 4.1, checked: an atlas equivalent to the
  atlas of `P` all of whose charts are corner charts, i.e. modelled on `(U, C, V)` with `U`
  relatively open in a partial quadrant `C` of a finite-dimensional `V` with the constant
  sc-structure and the identity retraction).
- `X_0 = X_∞`: `P.smoothSet = Set.univ` (`X_∞ = ⋂ X_m`).
- `X^1` is the project's `P.shift` (the level `X_1` with the charts `(V₁, φ, (O₁, C₁, E¹))`, the
  paragraph after Definition 2.14); its paracompactness is a project instance found by instance
  search.  `1_0^1 : X → X^1` is `P.toLevelOne x₀` (checked: `x ↦ x` on `X_1`, junk `x₀` off
  `X_1`); since `X_0 = X_∞ ⊆ X_1` is asserted alongside, the junk is never used, and B asks the
  sc-smoothness for every junk value `x₀`.
- "tame chart `(V, ψ, (O, C, E))`": a chart of the M-polyfold structure (`P.IsChart ψ`, i.e.
  compatible with the atlas) whose model `(O, C, E)` is a tame retract (`IsTameRetract`,
  Definition 2.34, checked: `O = r(U)` for a tame sc-smooth retraction `r`).  `x` lies in its
  domain and `ψ(x) = 0`.
- `T_0O`: the project's `tangentSpace E C O 0` (Definition 2.17, checked: the fibre over `0 ∈ O₁`
  of `TO = Tr(TU)` for a chosen retraction `r` onto `O`, i.e. `Dr(0)E`, independent of `r`), as
  the carrier of a linear subspace `N` of `E₀`; "finite-dimensional" is `FiniteDimensional ℝ N`,
  and "in good position to `C`" is the project's `IsInGoodPosition E C N` (Definition 3.21, checked:
  `N ∩ C` has nonempty interior in `N` and `N` has a good complement `Y`, `E₀ = N ⊕ Y`, with an
  `ε > 0` such that `|y| ≤ ε|n|` implies `n ∈ C ↔ n + y ∈ C`).  The project's good complement is
  an algebraic complement (its docstring: the text asks for an sc-complement); for a
  finite-dimensional smooth `N` I accepted this.
- Nothing looks false to me.
-/
namespace RoundTrip.V4_5
open Polyfold

/-- Theorem 4.2: a tame M-polyfold has a compatible structure of a smooth manifold with boundary
with corners iff `X_0 = X_∞`, `1_0^1 : X → X^1` is sc-smooth, and every point is the centre of a
tame chart whose tangent space at `0` is finite-dimensional and in good position to the partial
quadrant. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X),
    P.IsTame →
      (P.HasCornerStructure ↔
        (P.smoothSet = Set.univ ∧
          (∀ x₀ : P.Level 1, P.IsScSmoothMap P.shift (P.toLevelOne x₀)) ∧
          ∀ x : X, ∃ ψ : MChart X,
            P.IsChart ψ ∧ IsTameRetract ψ.model.E ψ.model.C ψ.model.O ∧
            x ∈ ψ.source ∧ ψ.toPartialEquiv x = 0 ∧
            ∃ N : Submodule ℝ (ψ.model.E.lvl 0),
              (N : Set (ψ.model.E.lvl 0)) = tangentSpace ψ.model.E ψ.model.C ψ.model.O 0 ∧
              FiniteDimensional ℝ N ∧ IsInGoodPosition ψ.model.E ψ.model.C N))

end RoundTrip.V4_5
