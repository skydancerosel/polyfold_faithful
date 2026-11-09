import Polyfold
/-! Blind formalization of V9_29 (the text's Part II, §9.3, p. 422 of the Springer 2021 book; 2017
p. 310, and Remark 9.3.1 (2017: Remark 9.7)): the category `Gr̂(X)` and oriented tangent spaces.

Text: `Gr̂(X)` is defined like `Gr(X)` with oriented finite-dimensional subspaces `(L, o)` of
`T_xX`; forgetting orientations is a functor `Gr̂(X) → Gr(X)` over `X^∞`.  Remark 9.3.1 recalls
an earlier notion of orientation.

Choices:
- Setting: `Obj Mor : Type` (universe 0), the project's `X : EpGroupoid Obj Mor`.
- Project notions used (all `#print`ed): `X.GrObj` / `X.GrHatObj` (pairs `(x, a)` with `x ∈ X_∞`
  and `a ∈ Gr(x)`, resp. `Gr̂(x)`), with their category structures (`#print`ed instances: a
  morphism `(x, a) → (y, b)` is a `φ : x → y` of `X` with `Tφ_*(a) = b`, composition that of `X`;
  this is the text's `((x, a), φ)` of Gr(X), V9_11), `X.grProj`, `X.grHatProj` (the projections to
  `X^∞ = X.SmoothCat`, the full subcategory of smooth objects).  For "oriented finite-dimensional
  linear subspace `(L, o)` of `T_xX`" the project's `X.PObj.IsOrientedAt x` on `OrTangent`
  (`#print`ed: a set `L` of tangent vectors over `x`, a dimension `n` and a set of frames, such
  that in a chart around `x` the chart vectors of `L` form an `n`-dimensional linear subspace `N`
  of `E₀` and the frames are the bases of `N` positive for an orientation of `N`); the project's
  `T_xX` has no linear structure, so a chart reading is unavoidable and I take this one.
- (a) "defined like `Gr(X)`": `Gr̂(x)` is the set of finite formal sums `∑ σ_{L̂} L̂` of such
  `L̂ = (L, o)`; weights rational and `≥ 0`, as the project's `Gr(x)` has them (V9_11 says
  "rational weights"; the nonnegativity is the `Gr` convention I copy).  B (a) says the project's
  `X.GrHat x` is this set of finitely supported functions.
- (b) "forgetting orientations is a functor `Gr̂(X) → Gr(X)` over `X^∞`": there is a functor `F`
  with `F(x, ∑ σ_{(L,o)} (L, o)) = (x, ∑ σ_{(L,o)} L)` (the linear extension of `(L, o) ↦ L`,
  `Finsupp.mapDomain carrier`), `F((x, a), φ) = (F(x, a), φ)` (same underlying morphism `φ`), and
  `π ∘ F = π̂` as functors to `X^∞` (`F ⋙ X.grProj = X.grHatProj`).  I write the forgetful map
  myself rather than using the project's `grForget`/`grForgetFunctor`.
- Remark 9.3.1 only recalls a notion; no claim, not formalized.
- Nothing looks false to me.
-/
namespace RoundTrip.V9_29
open Polyfold CategoryTheory

/-- `Gr̂(X)` and the forgetful functor: (a) `Gr̂(x)` consists of the finite formal sums with
weights `≥ 0` of oriented finite-dimensional subspaces of `T_xX`; (b) forgetting orientations is
a functor `Gr̂(X) → Gr(X)` over `X^∞`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    -- (a) the fibres `Gr̂(x)`
    (∀ (x : Obj) (w : X.PObj.OrTangent →₀ ℚ),
      w ∈ X.GrHat x ↔ ((∀ g, 0 ≤ w g) ∧ ∀ g ∈ w.support, X.PObj.IsOrientedAt x g)) ∧
    -- (b) the forgetful functor over `X^∞`
    (∃ F : X.GrHatObj ⥤ X.GrObj,
      (∀ a : X.GrHatObj, (F.obj a).pt = a.pt ∧
        (F.obj a).sum = Finsupp.mapDomain MPolyfold.OrTangent.carrier a.sum) ∧
      (∀ (a b : X.GrHatObj) (f : a ⟶ b), (F.map f).1 = f.1) ∧
      F ⋙ X.grProj = X.grHatProj)

end RoundTrip.V9_29
