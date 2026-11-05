import Polyfold
/-! Blind formalization of V4_1 (the text's §4.1, Definition 4.1, p. 147).

Text: an M-polyfold `X` has a compatible smooth manifold structure with boundary with corners if
it admits an atlas of sc-smoothly compatible charts `(V, φ, (U, C, ℝⁿ))`, `φ : V → U` an
sc-diffeomorphism from an open `V ⊆ X` onto a relatively open subset `U` of a partial quadrant
`C` in `ℝⁿ` (or in a finite-dimensional vector space).

Choices:
- This item is a definition.  B says that the project's notion is the text's:
  `P.HasCornerStructure ↔ HasCornerStructureB P` for every M-polyfold.
- Setting: `X : Type` (universe 0), Hausdorff paracompact, `P : MPolyfold X` (Definition 2.13).
  Charts are the project's `MChart X` (Definition 2.11, checked with `#print`: a local model
  `(O, C, E)` and a homeomorphism `φ` from an open `V ⊆ X` onto `O`, as a `PartialEquiv`).
- Corner chart `(V, φ, (U, C, ℝⁿ))`, my `IsCornerChartB`: the model space `E` is
  finite-dimensional (`FiniteDimensional ℝ E₀`) and carries the constant sc-structure (every
  composite inclusion `E_m → E₀` is onto; this is automatic by V4_3, kept because the text's
  `ℝⁿ` carries it), and the model set `O = U` is a relatively open subset of the partial quadrant
  `C` (`IsRelOpenInQuadrant`, checked: `C` a partial quadrant in the sense of Definition 1.11 and
  `U = W ∩ C`, `W` open).  The identity of `U` is then the retraction of the model.  Reading of
  "ℝⁿ (or a finite-dimensional vector space)": ANY finite-dimensional sc-Banach space, not only the
  project's literal representative `ScBanach.const V`; by V4_3 these are the same sc-spaces up to
  the identification of levels, so the M-polyfold-level notion should not change.  (The project's
  chart-level `MChart.IsCornerChart` asks `model = LocalModel.ofRelOpen hU` over
  `ScBanach.const V`, a stricter chart-level condition; B compares only the structure-level
  notions.)
- "an atlas of sc-smoothly compatible charts": a set `S` of charts, pairwise sc-smoothly
  compatible (the project's `MChart.Compatible`, Definition 2.11, checked: both transition maps
  are sc-smooth between the overlap retracts) and covering `X`.
- "compatible" (structure compatible with the M-polyfold `X`) and "`φ` an sc-diffeomorphism from
  the open `V ⊆ X`" (with respect to the M-polyfold structure of `X`): every chart of `S` is a
  chart of the M-polyfold structure, `P.IsChart χ` (checked: compatible with every chart of the
  atlas of `P`).  Since `Compatible` is symmetric, this is the same as "`S` together with the
  atlas of `P` is an atlas" (equivalence of atlases, Definition 2.12).
- The dimension may vary from chart to chart (the text fixes no `n`).
- Nothing looks false to me.
-/
namespace RoundTrip.V4_1
open Polyfold

/-- A **corner chart** `(V, φ, (U, C, ℝⁿ))`: the model sc-space is finite-dimensional with the
constant sc-structure, and the model set is a relatively open subset `U` of a partial quadrant
`C`. -/
def IsCornerChartB {X : Type} [TopologicalSpace X] (χ : MChart X) : Prop :=
  FiniteDimensional ℝ (χ.model.E.lvl 0) ∧
  (∀ m : ℕ, Function.Surjective (χ.model.E.toBase m)) ∧
  IsRelOpenInQuadrant χ.model.E χ.model.C χ.model.O

/-- An atlas of pairwise sc-smoothly compatible corner charts covering `X`, compatible with the
M-polyfold structure `P`. -/
def IsCornerAtlasB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) (S : Set (MChart X)) : Prop :=
  (∀ χ ∈ S, IsCornerChartB χ) ∧
  (∀ χ ∈ S, ∀ χ' ∈ S, χ.Compatible χ') ∧
  (∀ x : X, ∃ χ ∈ S, x ∈ χ.source) ∧
  (∀ χ ∈ S, P.IsChart χ)

/-- **Definition 4.1**: the M-polyfold `X` has a compatible smooth manifold structure with
boundary with corners. -/
def HasCornerStructureB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) : Prop :=
  ∃ S : Set (MChart X), IsCornerAtlasB P S

/-- Definition 4.1: the project's `HasCornerStructure` is the text's notion. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X),
    P.HasCornerStructure ↔ HasCornerStructureB P

end RoundTrip.V4_1
