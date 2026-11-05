import Polyfold
/-! Blind formalization of V2_10 (the text's §2.2, Definition 2.11, pp. 23–24).

Text: a chart around `x` in a space `X` is `(V, φ, (O, C, E))` with `V` an open neighbourhood of
`x`, `(O, C, E)` an sc-smooth retract and `φ : V → O` a homeomorphism.  Two charts are
sc-smoothly compatible if `ψ ∘ φ⁻¹ : φ(V ∩ V') → ψ(V ∩ V')` and its inverse are sc-smooth
(Definition 2.7); `φ(V ∩ V')` is a retract by Proposition 2.10(1).

Choices:
- This item is a definition plus a property.  Setting: a topological space `X : Type` (spaces put
  in `Type`; the project's `MChart` is universe-polymorphic, this is the instance `u = 0`).  No
  separation axiom is needed for the definition.
- The retract `(O, C, E)` is a project `LocalModel` `M` (checked with `#print`: a structure with
  fields `E : ScBanach`, `C O : Set (E.lvl 0)` and a proof of `IsScRetract E C O`, which is
  Definition 2.3 — see my `RoundTrip/Blind/V2_2.lean`).
- A chart is given by `V : Set X`, `M` and a total map `φ : X → E₀` (only its values on `V`
  matter).  `IsChartB V M φ`: `V` is open and the restriction of `φ` is a homeomorphism `V ≃ₜ O`
  (subspace topologies).  "Around `x`": `x ∈ V` (`IsChartAtB`).
- Compatibility (`CompatibleB`): with `A = φ(V ∩ V')`, `A' = ψ(V ∩ V')`, the transition
  `ψ ∘ φ⁻¹` is the total map `transB` (`y ↦ ψ(x)` for the point `x ∈ V` with `φ(x) = y`, which is
  unique and lies in `V'` when `y ∈ A`; junk `0` otherwise — only values on `A` matter), and both
  `ψ ∘ φ⁻¹ : (A, C, E) → (A', C', E')` and `φ ∘ ψ⁻¹ : (A', C', E') → (A, C, E)` are sc-smooth in
  the sense of Definition 2.7, read existentially (`IsScSmoothRetractMapB`: maps `A` into `A'` and
  `f ∘ r` is sc-smooth for SOME retraction `r` onto `A`, as in `RoundTrip/Blind/V2_6.lean`).
  The retract `(φ(V ∩ V'), C, E)` uses the partial quadrant `C` of the chart's own model.
- B: (a) every project chart `MChart X` (checked with `#print`: a `LocalModel` and a
  `PartialEquiv X E₀` with open source, target `O`, continuous on source and inverse continuous on
  `O`) is a chart in my sense; (b) conversely every chart around a point `x` in my sense is
  (agrees on `V` with) a project chart with the same model and source (stated with a cast `h ▸`
  along `c.model = M`).  The text speaks of charts AROUND a point; for the empty chart on an empty
  space there is no `PartialEquiv X E₀` (its inverse would be a map `E₀ → ∅`), so (b) is only
  asserted for charts around a point;
  (c) the project's `MChart.Compatible` is `CompatibleB`; (d) the claim "`φ(V ∩ V')` is a
  retract" (Proposition 2.10(1)), for any two charts.
- Nothing looks false to me.
-/
namespace RoundTrip.V2_10
open Polyfold

/-- **Definition 2.7**: `f : O → O'` is sc-smooth between the retracts `(O, C, E)` and
`(O', C', E')`: `f(O) ⊆ O'` and `f ∘ r` is sc-smooth for a retraction `r` onto `O`. -/
def IsScSmoothRetractMapB (E : ScBanach) (C O : Set (E.lvl 0)) (E' : ScBanach)
    (O' : Set (E'.lvl 0)) (f : E.lvl 0 → E'.lvl 0) : Prop :=
  Set.MapsTo f O O' ∧ ∃ R : ScRetraction E C, R.retract = O ∧ IsScSmooth R.U (f ∘ R.toFun)

variable {X : Type} [TopologicalSpace X]

/-- **Definition 2.11**: `(V, φ, (O, C, E))` is a chart: `V ⊆ X` open, `(O, C, E) = M` an
sc-smooth retract, and `φ : V → O` a homeomorphism. -/
def IsChartB (V : Set X) (M : LocalModel) (φ : X → M.E.lvl 0) : Prop :=
  IsOpen V ∧ ∃ e : V ≃ₜ M.O, ∀ x : V, (e x : M.E.lvl 0) = φ x

/-- A chart around `x`. -/
def IsChartAtB (x : X) (V : Set X) (M : LocalModel) (φ : X → M.E.lvl 0) : Prop :=
  x ∈ V ∧ IsChartB V M φ

open Classical in
/-- The transition map `ψ ∘ φ⁻¹`, as a total map `E₀ → E'₀` (junk `0` off `φ(V)`). -/
noncomputable def transB (V : Set X) {M : LocalModel} (φ : X → M.E.lvl 0) {M' : LocalModel}
    (ψ : X → M'.E.lvl 0) : M.E.lvl 0 → M'.E.lvl 0 :=
  fun y => if h : ∃ x ∈ V, φ x = y then ψ (Classical.choose h) else 0

/-- **Definition 2.11**: the charts `(V, φ, M)` and `(V', ψ, M')` are sc-smoothly compatible:
`ψ ∘ φ⁻¹ : φ(V ∩ V') → ψ(V ∩ V')` and its inverse are sc-smooth (Definition 2.7). -/
def CompatibleB (V : Set X) (M : LocalModel) (φ : X → M.E.lvl 0)
    (V' : Set X) (M' : LocalModel) (ψ : X → M'.E.lvl 0) : Prop :=
  IsScSmoothRetractMapB M.E M.C (φ '' (V ∩ V')) M'.E (ψ '' (V ∩ V')) (transB V φ ψ) ∧
  IsScSmoothRetractMapB M'.E M'.C (ψ '' (V ∩ V')) M.E (φ '' (V ∩ V')) (transB V' ψ φ)

/-- Definition 2.11: the project's charts and their compatibility are the text's; and the overlap
`φ(V ∩ V')` of two charts is a retract. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X],
    -- (a) project charts are charts
    (∀ (c : MChart X) (x : X), x ∈ c.source →
      IsChartAtB x c.source c.model (c.toPartialEquiv : X → c.model.E.lvl 0)) ∧
    -- (b) every chart (around some point) is a project chart
    (∀ (x : X) (V : Set X) (M : LocalModel) (φ : X → M.E.lvl 0), IsChartAtB x V M φ →
      ∃ (c : MChart X) (h : c.model = M), c.source = V ∧
        ∀ x ∈ V, φ x = h ▸ (c.toPartialEquiv x)) ∧
    -- (c) compatibility
    (∀ c c' : MChart X, c.Compatible c' ↔
      CompatibleB c.source c.model (c.toPartialEquiv : X → c.model.E.lvl 0)
        c'.source c'.model (c'.toPartialEquiv : X → c'.model.E.lvl 0)) ∧
    -- (d) `φ(V ∩ V')` is a retract
    (∀ (V : Set X) (M : LocalModel) (φ : X → M.E.lvl 0)
      (V' : Set X) (M' : LocalModel) (ψ : X → M'.E.lvl 0),
      IsChartB V M φ → IsChartB V' M' ψ → IsScRetract M.E M.C (φ '' (V ∩ V')))

end RoundTrip.V2_10
