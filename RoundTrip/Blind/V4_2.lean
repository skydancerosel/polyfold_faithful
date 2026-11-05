import Polyfold
/-! Blind formalization of V4_2 (the text's §4.1, after Definition 4.1, p. 147).

Text: the transition maps between the charts are sc-diffeomorphisms between relatively open
subsets of partial quadrants in finite-dimensional spaces, and therefore classically smooth, of
class `C^∞`; the atlas defines the structure of a smooth manifold with boundary with corners.

Choices:
- Setting: that of Definition 4.1 (my V4_1): `X : Type` (universe 0), Hausdorff paracompact,
  `P : MPolyfold X`, and an atlas `S` of corner charts in the sense of Definition 4.1
  (`IsCornerAtlasB`, copied from V4_1: every chart is modelled on a relatively open subset `U` of
  a partial quadrant `C` of a finite-dimensional sc-space with the constant sc-structure; charts
  pairwise sc-smoothly compatible (`MChart.Compatible`), covering `X`, and charts of `P`).
- "the transition maps between the charts": for `χ, χ' ∈ S`, the map `χ' ∘ χ⁻¹` (`transB`) on
  the overlap `χ(V ∩ V')` (`overlapB`).  "sc-diffeomorphisms between relatively open subsets of
  partial quadrants": the overlap is relatively open in the partial quadrant `C` of `χ`
  (`IsRelOpenInQuadrant`), `χ' ∘ χ⁻¹` maps it into the overlap `χ'(V ∩ V')`, `χ ∘ χ'⁻¹` inverts it
  there, and `χ' ∘ χ⁻¹` is sc-smooth on it (`IsScSmooth`, Definition 1.15; the inverse is the same
  statement with `χ, χ'` swapped).
- "classically smooth, of class `C^∞`": Mathlib's `ContDiffOn ℝ ∞` on the overlap (derivatives
  within the set, which is locally a convex set with nonempty interior); `∞` is written
  `((⊤ : ℕ∞) : WithTop ℕ∞)` (not `ω`).
- "the atlas defines the structure of a smooth manifold with boundary with corners": the
  classical notion, my own `IsClassicalCornerAtlasB`: every chart maps an open subset of `X`
  homeomorphically (built into `MChart`) onto a relatively open subset of a classical partial
  quadrant `T⁻¹([0,∞)ᵏ × ℝˡ)` (`T` a linear isomorphism, my `IsClassicalQuadrantB`, not the sc
  notion) of a finite-dimensional normed space; the charts cover `X`; overlaps are relatively
  open; transition maps are `C^∞`.  Dimensions may vary from chart to chart.  (Mathlib's
  `IsManifold` needs one fixed model space, so I did not use it.)
- Nothing looks false to me.
-/
namespace RoundTrip.V4_2
open Polyfold

/-- A corner chart (Definition 4.1, as in V4_1). -/
def IsCornerChartB {X : Type} [TopologicalSpace X] (χ : MChart X) : Prop :=
  FiniteDimensional ℝ (χ.model.E.lvl 0) ∧
  (∀ m : ℕ, Function.Surjective (χ.model.E.toBase m)) ∧
  IsRelOpenInQuadrant χ.model.E χ.model.C χ.model.O

/-- An atlas of corner charts for the M-polyfold `P` (Definition 4.1, as in V4_1). -/
def IsCornerAtlasB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) (S : Set (MChart X)) : Prop :=
  (∀ χ ∈ S, IsCornerChartB χ) ∧
  (∀ χ ∈ S, ∀ χ' ∈ S, χ.Compatible χ') ∧
  (∀ x : X, ∃ χ ∈ S, x ∈ χ.source) ∧
  (∀ χ ∈ S, P.IsChart χ)

/-- The overlap `χ(V ∩ V')`, in the model space of `χ`. -/
def overlapB {X : Type} [TopologicalSpace X] (χ χ' : MChart X) : Set (χ.model.E.lvl 0) :=
  χ.toPartialEquiv '' (χ.toPartialEquiv.source ∩ χ'.toPartialEquiv.source)

/-- The transition map `χ' ∘ χ⁻¹`. -/
def transB {X : Type} [TopologicalSpace X] (χ χ' : MChart X) :
    χ.model.E.lvl 0 → χ'.model.E.lvl 0 :=
  χ'.toPartialEquiv ∘ χ.toPartialEquiv.symm

/-- A classical partial quadrant of a finite-dimensional space: `T⁻¹([0,∞)ᵏ × ℝˡ)` for a linear
isomorphism `T : V ≃ ℝᵏ × ℝˡ`. -/
def IsClassicalQuadrantB {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (C : Set V) :
    Prop :=
  ∃ (k l : ℕ) (T : V ≃L[ℝ] (Fin k → ℝ) × (Fin l → ℝ)), C = T ⁻¹' {p | ∀ i, 0 ≤ p.1 i}

/-- `U` is relatively open in `C`. -/
def IsRelOpenInB {V : Type} [TopologicalSpace V] (C U : Set V) : Prop :=
  ∃ W : Set V, IsOpen W ∧ U = W ∩ C

/-- A classical smooth atlas with boundary with corners: charts are homeomorphisms (built into
`MChart`) from open subsets of `X` onto relatively open subsets of classical partial quadrants of
finite-dimensional spaces, covering `X`, with relatively open overlaps and `C^∞` transition
maps. -/
def IsClassicalCornerAtlasB {X : Type} [TopologicalSpace X] (S : Set (MChart X)) : Prop :=
  (∀ χ ∈ S, FiniteDimensional ℝ (χ.model.E.lvl 0) ∧ IsClassicalQuadrantB χ.model.C ∧
    IsRelOpenInB χ.model.C χ.model.O) ∧
  (∀ x : X, ∃ χ ∈ S, x ∈ χ.toPartialEquiv.source) ∧
  (∀ χ ∈ S, ∀ χ' ∈ S, IsRelOpenInB χ.model.C (overlapB χ χ') ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (transB χ χ') (overlapB χ χ'))

/-- After Definition 4.1: the transition maps of a corner atlas are sc-diffeomorphisms between
relatively open subsets of partial quadrants, hence `C^∞`, and the atlas is a classical smooth
atlas with boundary with corners. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
    (S : Set (MChart X)), IsCornerAtlasB P S →
    (∀ χ ∈ S, ∀ χ' ∈ S,
      -- sc-diffeomorphisms between relatively open subsets of partial quadrants
      IsRelOpenInQuadrant χ.model.E χ.model.C (overlapB χ χ') ∧
      Set.MapsTo (transB χ χ') (overlapB χ χ') (overlapB χ' χ) ∧
      (∀ z ∈ overlapB χ χ', transB χ' χ (transB χ χ' z) = z) ∧
      IsScSmooth (E := χ.model.E) (F := χ'.model.E) (overlapB χ χ') (transB χ χ') ∧
      -- classically smooth, `C^∞`
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (transB χ χ') (overlapB χ χ')) ∧
    -- the atlas defines a smooth manifold structure with boundary with corners
    IsClassicalCornerAtlasB S

end RoundTrip.V4_2
