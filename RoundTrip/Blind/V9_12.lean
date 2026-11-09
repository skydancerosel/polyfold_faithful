import Polyfold
/-! Blind formalization of V9_12 (the Springer 2021 book, Part II, §9.2, before Theorem 9.2.1,
p. 409 [2017 p. 298], with Part I, Remark 4.2.2): the tangent space `T_yM` of a submanifold, set
form and chart form.

Text: for a submanifold `M` (the image of an sc⁺-retraction `r`) and `y ∈ M`,
`T_yM = Tr(y)(T_yX)`, a finite-dimensional linear subspace of `T_yX`.

Choices:
- Setting: `Z : Type` (universe 0), Hausdorff paracompact, `P : MPolyfold Z`; `M` a smooth
  finite-dimensional submanifold, the project's `P.IsSmoothSubmanifold M` (Part I Definition 4.13 of
  the preprint, compared in `RoundTrip/Blind/V4_29.lean`), with its data `P.SubmanifoldData M`
  (`#print`ed: an open `V`, an sc⁺-retraction `r = d.s` on `V`, `r(V) = M ∩ V`).
- `Tr(y)`: the project's `d.tmap` (vocabulary: `Tr : TV → TV`, the tangent map of the
  sc⁺-retraction of the data), applied to the vectors over `y` (`T_yX = TxXB P y`), for data with
  `y ∈ V`.  "Set form": `T_yM := Tr(y)(T_yX)`, a set of tangent vectors.
- The claims I read into the definition: (a) `Tr(y)(T_yX)` does not depend on the data
  `(V, r)` at `y` (otherwise "`T_yM`" is not defined); (b) it lies in `T_yX` and is a
  finite-dimensional linear subspace of it.  The project's `T_yX` has no linear structure, so (b)
  is read in charts ("chart form"): for EVERY chart `φ` of the structure around `y`, the second
  components `h` of `Tφ(α) = (φ(y), h)` (the project's `tangentChartMap`, compared with the
  text's `Tφ` in `RoundTrip/Blind/V2_19.lean`), `α ∈ T_yM`, form a finite-dimensional linear
  subspace of `E₀` (every chart, since the claim is about the linear structure of `T_yX`, which
  every chart induces).  (c) The project's `P.submanifoldTangent M y` is this set.
- Nothing looks false to me.
-/
namespace RoundTrip.V9_12
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

end

/-- `T_yM = Tr(y)(T_yX)` is well defined, is a finite-dimensional linear subspace of `T_yX` in
every chart, and is the project's `submanifoldTangent`. -/
def B : Prop :=
  ∀ (Z : Type) [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] (P : MPolyfold Z)
    (M : Set Z), P.IsSmoothSubmanifold M → ∀ y ∈ M,
    -- (a) independent of the sc⁺-retraction
    (∀ d d' : P.SubmanifoldData M, y ∈ d.V → y ∈ d'.V →
      d.tmap '' TxXB P y = d'.tmap '' TxXB P y) ∧
    -- (b) a finite-dimensional linear subspace of `T_yX`, in every chart
    (∀ d : P.SubmanifoldData M, y ∈ d.V →
      d.tmap '' TxXB P y ⊆ TxXB P y ∧
      ∀ (φ : MChart Z) (hφ : P.IsChart φ), y ∈ φ.source →
        ∃ S : Submodule ℝ (φ.model.E.lvl 0), FiniteDimensional ℝ S ∧
          chartImgB hφ (d.tmap '' TxXB P y) = (S : Set (φ.model.E.lvl 0))) ∧
    -- (c) the project's `T_yM`
    (∀ d : P.SubmanifoldData M, y ∈ d.V → P.submanifoldTangent M y = d.tmap '' TxXB P y)

end RoundTrip.V9_12
