import Polyfold
/-! Blind formalization of V9_36 (the text's Part II, §9.3, Definition 9.3.8, p. 427 of the
Springer 2021 book; 2017: Definition 9.9, p. 313): the boundary orientation of an oriented `M`.

Text: for an oriented `n`-dimensional `(M, o)` and `y ∈ ∂M` with `d_M(y) = 1`, a basis
`(a₁, …, a_{n-1})` of `T_y∂M` is positive iff `(e, a₁, …, a_{n-1})` is positive for `o_y`, `e` an
outward pointing vector; this orients `∂M` near `y`.

Choices:
- Setting: the text's `M` is a manifold with boundary with corners (the sheets of §9.3, V9_34);
  in the project's vocabulary: `Z : Type` (universe 0), an M-polyfold `P : MPolyfold Z`, and `M` a
  smooth `n`-dimensional submanifold (`IsSubmanifoldOfDim`, V9_2) with tame induced structure
  (`HasTameInducedStructure`, `#print`ed), so that `M` is a manifold with boundary with corners.
  No tameness of `P` is assumed.  `n = m + 1` (a point with `d_M(y) = 1` forces `n ≥ 1`).
- `o`: the project's `SubmanifoldOrientation M (m+1)` (`#print`ed: positive frames `o.frames y`
  of `T_yM`, continuous in charts).  "positive for `o_y`": membership in `o.frames y`.
- `d_M(y)`: my `dMB` (the project's `subDegIndex` of the induced structure, as in
  `RoundTrip/Blind/V9_35.lean`).  `∂M`: the project's `submanifoldBoundary M` (`d_M ≥ 1`).
  `T_y∂M`: the project's `submanifoldTangent (∂M) y` (the tangent space of the set `∂M`, which near
  `y` is a submanifold); in (b) of the piece `∂M ∩ V`.
- "outward pointing vector `e`" (my `IsOutwardB`; the project's `T_yX` has no linear structure,
  so I read it in charts): `e ∈ T_yM` and, in every chart `φ` of `P` around `y`, the chart vector
  of `e` (`chartVec`, the `h` of `Tφ(e) = (φ(y), h)`) is not in Mathlib's positive tangent cone
  `posTangentConeAt (φ(M ∩ dom φ)) (φ(y))` (the inward and tangential directions of `M`).
- "a basis `a` of `T_y∂M` is positive iff `(e, a)` is positive": the set of frames
  `{a : Fin m → TZ | ∀ i, aᵢ ∈ T_y∂M, (e, a) ∈ o.frames y}` (`bdFramesB`, `Fin.cons e a`; a frame
  of `T_y∂M` completed by `e` to a positive basis is itself a basis).
- B asserts what the definition presupposes and states: (a) outward vectors exist at `y` and the
  set of positive frames does not depend on the outward vector chosen; (b) "this orients `∂M`
  near `y`": for some open `V ∋ y`, `∂M ∩ V` is an `m`-dimensional submanifold with an orientation
  (project's `SubmanifoldOrientation`) whose positive frames at every `z ∈ ∂M ∩ V` are exactly
  those given by the rule, for every outward `e` at `z` (and outward vectors exist there).
- Nothing looks false to me.
-/
namespace RoundTrip.V9_36
open Polyfold

section
variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]

open Classical in
/-- `d_M(y)`: the degeneracy index of `y` for the structure induced on the sub-M-polyfold `M`
(`0` if `M` is not a sub-M-polyfold or `y ∉ M`). -/
noncomputable def dMB (P : MPolyfold Z) (M : Set Z) (y : Z) : ℕ :=
  if h : P.IsSubMPolyfold M ∧ y ∈ M then P.subDegIndex h.1 ⟨y, h.2⟩ else 0

/-- `e` is an outward pointing vector of `M` at `y`: `e ∈ T_yM` and in every chart around `y` its
chart vector lies outside the positive tangent cone of the chart image of `M` at `y`. -/
def IsOutwardB (P : MPolyfold Z) (M : Set Z) (y : Z) (e : P.TangentSpace) : Prop :=
  e ∈ P.submanifoldTangent M y ∧
  ∀ (φ : MChart Z) (hφ : P.IsChart φ), y ∈ φ.source →
    MPolyfold.chartVec hφ e ∉
      posTangentConeAt (φ.toPartialEquiv '' (M ∩ φ.source)) (φ.toPartialEquiv y)

/-- The frames `a` of `K` with `(e, a)` positive for the frames `O`. -/
def bdFramesB {P : MPolyfold Z} {m : ℕ} (O : Set (Fin (m + 1) → P.TangentSpace))
    (K : Set P.TangentSpace) (e : P.TangentSpace) : Set (Fin m → P.TangentSpace) :=
  {a | (∀ i, a i ∈ K) ∧ (Fin.cons e a : Fin (m + 1) → P.TangentSpace) ∈ O}

end

/-- **Definition 9.3.8**: at a point `y` with `d_M(y) = 1` of an oriented `(m+1)`-dimensional
`(M, o)`, outward vectors exist, the frames `a` of `T_y∂M` with `(e, a)` positive do not depend on
the outward `e`, and they orient `∂M` near `y`. -/
def B : Prop :=
  ∀ (Z : Type) [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] (P : MPolyfold Z)
    (M : Set Z) (m : ℕ), P.IsSubmanifoldOfDim M (m + 1) → P.HasTameInducedStructure M →
    ∀ (o : P.SubmanifoldOrientation M (m + 1)) (y : Z), y ∈ M → dMB P M y = 1 →
      -- (a) existence of outward vectors, independence of the choice
      ((∃ e, IsOutwardB P M y e) ∧
        ∀ e e', IsOutwardB P M y e → IsOutwardB P M y e' →
          bdFramesB (o.frames y) (P.submanifoldTangent (P.submanifoldBoundary M) y) e =
            bdFramesB (o.frames y) (P.submanifoldTangent (P.submanifoldBoundary M) y) e') ∧
      -- (b) the boundary orientation of `∂M` near `y`
      (∃ V : Set Z, IsOpen V ∧ y ∈ V ∧ P.IsSubmanifoldOfDim (P.submanifoldBoundary M ∩ V) m ∧
        ∃ o' : P.SubmanifoldOrientation (P.submanifoldBoundary M ∩ V) m,
          ∀ z ∈ P.submanifoldBoundary M ∩ V, (∃ e, IsOutwardB P M z e) ∧
            ∀ e, IsOutwardB P M z e →
              o'.frames z = bdFramesB (o.frames z)
                (P.submanifoldTangent (P.submanifoldBoundary M ∩ V) z) e)

end RoundTrip.V9_36
