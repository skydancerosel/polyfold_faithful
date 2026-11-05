import Polyfold
/-! Blind formalization of V4_55 (the text's §4.3, Remark 4.24, p. 165).

Text: "By Proposition 2.36 the codimension of `T^R_xX` is `d_X(x)`; so for `λ ∈ Σ` a point of `A_λ`
can lie in a corner only if `d_X(x) ≤ dim A_λ`; zero-dimensional `A_λ` lie in `X \ ∂X`."

Choices:
- Setting: `X : Type` (universe 0, as in the other blind files of this chapter), Hausdorff,
  paracompact, `P : MPolyfold X` tame (`P.IsTame`, Definition 2.37: an equivalent atlas of charts
  on tame retracts — a property of the given structure).  B is the conjunction of three claims.
- (a) "the codimension of `T^R_xX` is `d_X(x)`" (in `T_xX`): read in a chart modelled on a tame
  retract (Definition 2.38 defines `T^R_xX` through tame charts), at the points of `X_∞`
  (`P.smoothSet`; Proposition 2.36 is stated at smooth points as I recall, and the remark only
  needs points of `A_λ ⊆ X_∞`).  For EVERY chart `φ` of the structure (`P.IsChart`) whose model is
  a tame retract (`IsTameRetract`, Definition 2.34), every presentation `T` of its partial quadrant
  and the level-`1` lift `z` of `φ(x)`: with `M = T_zO` (`tangentSpace`, Definition 2.17) and
  `T^R_zO = T_zO ∩ E_z` (`E_z = minimalSubspaceWith T z`, the vectors whose coordinates vanish where
  those of `z` do; Definitions 2.27, 2.38), `dim (T_zO / T^R_zO) = d_X(x)` (`Module.rank` of the
  quotient, as a cardinal; `d_X` is the project's `degIndex`, Definition 2.22).
- (b), (c): "for `λ ∈ Σ`": by Theorem 4.23, for `λ ∈ Σ` the fibre `A_λ` is a smooth
  finite-dimensional submanifold of `X` in general position at each of its points, and the
  reasoning of the remark uses nothing else.  I state (b), (c) for EVERY smooth
  finite-dimensional submanifold `A'` of `X` (the project's `IsSmoothSubmanifold`, Definition
  4.13) and every point `x ∈ A'` at which `A'` is in general position (the project's
  `IsGeneralPositionAt`, Definition 4.21).  This is more general than the text's "`A_λ`,
  `λ ∈ Σ`" (it does not refer to the set `Σ` of Theorem 4.23, which the theorem only asserts to
  exist); every such `A_λ` is a case.
- "`dim A_λ`" at `x`: the dimension of the tangent space `T_xA'`, read in a chart: data
  `(V, s)` of Definition 4.13 at `x` (the project's `IsScPlusRetractionOn`, `s(V) = A' ∩ V`), a
  chart `φ` of the structure with `V` in its domain, the level-`1` lift `z` of `φ(x)`, and
  `N = T_z(φ(A' ∩ V))`.  (b) "a point can lie in a corner only if `d_X(x) ≤ dim A_λ`": for every
  such data, chart and lift, `d_X(x) ≤ dim N` (`Module.rank`); stated for every point, as it is
  trivial when `d_X(x) = 0`.  (c) "zero-dimensional `A_λ` lie in `X \ ∂X`", pointwise: if
  `dim N = 0` for some such data, chart and lift (the weakest form of "zero-dimensional at `x`"),
  then `x ∉ ∂X` (`P.boundary = {d_X ≥ 1}`, Definition 2.25).
- Nothing looks false to me.
-/
namespace RoundTrip.V4_55
open Polyfold

/-- Remark 4.24: the reduced tangent space has codimension `d_X(x)`; hence a submanifold in general
position at `x` has dimension at least `d_X(x)` there, and a zero-dimensional one does not meet
`∂X`. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X),
    P.IsTame →
    -- (a) Proposition 2.36: `codim T^R_xX = d_X(x)`
    (∀ (φ : MChart X) (n : ℕ) (Wq : ScBanach)
      (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq)) (x : X)
      (z : φ.model.E.lvl 1) (M : Submodule ℝ (φ.model.E.lvl 0)),
      P.IsChart φ → IsTameRetract φ.model.E φ.model.C φ.model.O →
      φ.model.C = T.lvl 0 ⁻¹' quadrant n Wq 0 →
      x ∈ φ.toPartialEquiv.source → x ∈ P.smoothSet →
      φ.model.E.toBase 1 z = φ.toPartialEquiv x →
      (M : Set (φ.model.E.lvl 0)) = tangentSpace φ.model.E φ.model.C φ.model.O z →
        Module.rank ℝ (M ⧸ Submodule.comap M.subtype
            (minimalSubspaceWith T (φ.model.E.toBase 1 z))) = (P.degIndex x : Cardinal)) ∧
    -- (b) `d_X(x) ≤ dim_x A'` for a submanifold `A'` in general position at `x`
    (∀ (A' : Set X) (x : X), P.IsSmoothSubmanifold A' → x ∈ A' → P.IsGeneralPositionAt A' x →
      ∀ (V : Set X) (s : X → X) (φ : MChart X) (z : φ.model.E.lvl 1)
        (N : Submodule ℝ (φ.model.E.lvl 0)),
        P.IsScPlusRetractionOn s V → s '' V = A' ∩ V → x ∈ V →
        P.IsChart φ → V ⊆ φ.toPartialEquiv.source →
        φ.model.E.toBase 1 z = φ.toPartialEquiv x →
        (N : Set (φ.model.E.lvl 0)) =
          tangentSpace φ.model.E φ.model.C (φ.toPartialEquiv '' (A' ∩ V)) z →
          (P.degIndex x : Cardinal) ≤ Module.rank ℝ N) ∧
    -- (c) zero-dimensional submanifolds in general position avoid `∂X`
    (∀ (A' : Set X) (x : X), P.IsSmoothSubmanifold A' → x ∈ A' → P.IsGeneralPositionAt A' x →
      (∃ (V : Set X) (s : X → X) (φ : MChart X) (z : φ.model.E.lvl 1)
        (N : Submodule ℝ (φ.model.E.lvl 0)),
        P.IsScPlusRetractionOn s V ∧ s '' V = A' ∩ V ∧ x ∈ V ∧
        P.IsChart φ ∧ V ⊆ φ.toPartialEquiv.source ∧
        φ.model.E.toBase 1 z = φ.toPartialEquiv x ∧
        (N : Set (φ.model.E.lvl 0)) =
          tangentSpace φ.model.E φ.model.C (φ.toPartialEquiv '' (A' ∩ V)) z ∧
        Module.rank ℝ N = 0) →
        x ∉ P.boundary)

end RoundTrip.V4_55
