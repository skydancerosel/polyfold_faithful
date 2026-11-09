import Polyfold
/-! Blind formalization of V9_11 (the Springer 2021 book, Part II, §9.2, p. 409; 2017
pp. 297–298): the category `Gr(X)`.

Text: for a smooth `x`, `Gr(x)` is the set of finite formal sums `∑ σ_L L` of finite-dimensional
linear subspaces `L ⊆ T_xX` with rational weights; a morphism `φ : x → y` maps them by `Tφ`;
`Gr(X)` is the category of pairs `(x, a)`, with the projection `π : Gr(X) → X^∞`.

Choices:
- This item is a definition.  B says that the project's `X.Gr x`, `X.GrObj` (with its category
  instance) and `X.grProj` are the text's objects.
- Setting: `Obj Mor : Type` (universe 0), the project's `X : EpGroupoid Obj Mor`; `X^∞` is the
  full subcategory of the smooth objects, the project's `X.SmoothCat` (vocabulary: Chapter 7's
  full subcategory on `X.PObj.smoothSet`), accessed through `SmoothCat.pt`, `SmoothCat.mor`.
- `T_xX`: the tangent vectors over `x` in the project's `TX` (`TxXB`).  The project's `T_xX` has
  no linear structure, so "finite-dimensional linear subspace `L ⊆ T_xX`" is read in a chart
  (`IsFinDimSubspaceB`): `L ⊆ T_xX` and, for some chart `φ` of the structure around `x`, the
  second components `h` of `Tφ(α) = (φ(x), h)`, `α ∈ L` (the project's `tangentChartMap`, compared
  with the text's `Tφ` in `RoundTrip/Blind/V2_19.lean`), form a finite-dimensional linear subspace
  of `E₀`.  (`Tφ` identifies `T_xX` linearly with `T_{φ(x)}O`; the notion does not depend on the
  chart.)
- "finite formal sums with rational weights": finitely supported `a : Set TX →₀ ℚ` whose support
  consists of such subspaces (`GrB`).  "Rational weights" is read literally as `σ_L ∈ ℚ` (signs
  not restricted); if the text means `ℚ⁺`, add `0 ≤ a L`.
- "a morphism `φ : x → y` maps them by `Tφ`": `φ_*(∑ σ_L L) = ∑ σ_L Tφ(L)` (`pushB`, a
  `Finsupp.mapDomain`), with `Tφ` the project's `tangentMor` (2017 Definition 7.4; see
  `RoundTrip/Blind/V7_5.lean`).
- "`Gr(X)` the category of pairs `(x, a)`": objects are the pairs `(x, a)`, `x ∈ X_∞`,
  `a ∈ Gr(x)`; the morphisms `(x, a) → (y, b)` are the `φ : x → y` with `φ_* a = b` (the pairs
  `(a, φ)`).  B: the project's objects are exactly these pairs (`pt`, `sum`), and its morphisms
  `o ⟶ o'` correspond bijectively, through `π = grProj`, to such `φ`.  The projection sends
  `(x, a)` to `x` and `(a, φ)` to `φ` (the latter is how B reads off the `φ` of a morphism).
- Nothing looks false to me.
-/
namespace RoundTrip.V9_11
open Polyfold

section
variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]

/-- `T_yX`: the tangent vectors over `y` (the fibre of `p : TX → X¹` over `y ∈ X₁`). -/
def TxXB (P : MPolyfold Z) (y : Z) : Set P.TangentSpace :=
  {α | P.levelVal 1 (P.tangentProj α) = y}

/-- The chart image `{h | (φ(y), h) = Tφ(α), α ∈ S}` of a set `S` of tangent vectors. -/
def chartImgB {P : MPolyfold Z} {φ : MChart Z} (hφ : P.IsChart φ) (S : Set P.TangentSpace) :
    Set (φ.model.E.lvl 0) :=
  (fun α => (MPolyfold.tangentChartMap hφ α).2) '' S

/-- `L` is a finite-dimensional linear subspace of `T_yX`: `L ⊆ T_yX`, and in a chart `φ` around
`y` (through which `T_yX` is identified with the linear subspace `T_{φ(y)}O` of `E₀`) `L` is a
finite-dimensional linear subspace. -/
def IsFinDimSubspaceB (P : MPolyfold Z) (y : Z) (L : Set P.TangentSpace) : Prop :=
  L ⊆ TxXB P y ∧
    ∃ (φ : MChart Z) (hφ : P.IsChart φ), y ∈ φ.source ∧
      ∃ S : Submodule ℝ (φ.model.E.lvl 0), FiniteDimensional ℝ S ∧
        chartImgB hφ L = (S : Set (φ.model.E.lvl 0))

end

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- `Gr(x)`: the finite formal sums `∑ σ_L · L` (`σ_L ∈ ℚ`) of finite-dimensional linear
subspaces `L ⊆ T_xX`, as finitely supported weights on sets of tangent vectors. -/
def GrB (X : EpGroupoid Obj Mor) (x : Obj) : Set (Set X.PObj.TangentSpace →₀ ℚ) :=
  {a | ∀ L ∈ a.support, IsFinDimSubspaceB X.PObj x L}

/-- The image `∑ σ_L · Tφ(L)` of a formal sum under (the tangent `Tφ` of) a morphism `φ`. -/
noncomputable def pushB (X : EpGroupoid Obj Mor) (φ : Mor) (a : Set X.PObj.TangentSpace →₀ ℚ) :
    Set X.PObj.TangentSpace →₀ ℚ :=
  Finsupp.mapDomain (fun L => X.tangentMor φ '' L) a

end

/-- `Gr(x)`, `Gr(X)` and `π : Gr(X) → X^∞` of the project are the text's. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    -- `Gr(x)` for smooth `x`
    (∀ x ∈ X.PObj.smoothSet, ∀ a : Set X.PObj.TangentSpace →₀ ℚ, a ∈ X.Gr x ↔ a ∈ GrB X x) ∧
    -- the objects of `Gr(X)` are the pairs `(x, a)`, `x ∈ X_∞`, `a ∈ Gr(x)`
    (∀ o : X.GrObj, o.pt ∈ X.PObj.smoothSet ∧ o.sum ∈ GrB X o.pt) ∧
    (∀ x ∈ X.PObj.smoothSet, ∀ a ∈ GrB X x, ∃ o : X.GrObj, o.pt = x ∧ o.sum = a) ∧
    (∀ o o' : X.GrObj, o.pt = o'.pt → o.sum = o'.sum → o = o') ∧
    -- the morphisms `(x, a) → (y, b)` are the `φ : x → y` with `φ_* a = b`
    (∀ (o o' : X.GrObj) (φ : Mor),
      (∃ f : o ⟶ o', EpGroupoid.SmoothCat.mor (X.grProj.map f) = φ) ↔
        (X.src φ = o.pt ∧ X.tgt φ = o'.pt ∧ o'.sum = pushB X φ o.sum)) ∧
    (∀ (o o' : X.GrObj) (f g : o ⟶ o'),
      EpGroupoid.SmoothCat.mor (X.grProj.map f) = EpGroupoid.SmoothCat.mor (X.grProj.map g) →
        f = g) ∧
    -- `π(x, a) = x`
    (∀ o : X.GrObj, EpGroupoid.SmoothCat.pt (X.grProj.obj o) = o.pt)

end RoundTrip.V9_11
