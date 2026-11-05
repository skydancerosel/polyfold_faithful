import Polyfold
/-! Blind formalization of V5_16 (the text's §5.3, Definition 5.9, p. 173, and §5.4.2,
Definition 5.29, p. 192).

Text: Definition 5.9: `X` admits sc-smooth bump functions if for every `x` and open `U(x)` there is
an sc-smooth `f : X → ℝ` with `f ≠ 0` and `supp(f) ⊆ U(x)`.  Definition 5.29: `f` "not
identically zero".

Choices:
- This item is a definition (stated twice).  B says that the project's
  `PX.AdmitsBumpFunctionsWeak` is the text's notion `AdmitsBumpB` written below.
- Setting: `X : Type` (universe 0, as asked) with `PX : MPolyfold X` (Definition 2.13).
- "`U(x)`": an open set `U ⊆ X` containing `x`; quantified over every `x ∈ X` and every such `U`.
- "sc-smooth `f : X → ℝ`": the project's `PX.IsScSmoothMap realPolyfold f` (Definition 2.14, with
  `ℝ` the M-polyfold `realPolyfold`, checked with `#print`: the single identity chart, modelled on
  `ℝ` with the constant sc-structure `realSc`).
- "`f ≠ 0`": `f` is not the zero function, the plain meaning of `f ≠ 0` for a function and the one
  Definition 5.29 spells out ("not identically zero"); so Definitions 5.9 and 5.29 define the same
  notion, `AdmitsBumpB`.
- "`supp(f)`": the closure in `X` of `{f ≠ 0}` (Mathlib's `tsupport f`).
- NOT USED: the project's `PX.AdmitsBumpFunctions`, whose docstring labels it "Definition 5.9" but
  reads `f ≠ 0` as `f(x) ≠ 0` (checked with `#print`) — a stronger notion than the text's literal
  one.  `BPointwise` below (not the item) records that reading.
- Nothing looks false to me.
-/
namespace RoundTrip.V5_16
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- **Definitions 5.9 and 5.29**: `X` admits sc-smooth bump functions: for every `x` and every
open neighbourhood `U` of `x` there is an sc-smooth `f : X → ℝ`, not identically zero, with
`supp(f) ⊆ U`. -/
def AdmitsBumpB (PX : MPolyfold X) : Prop :=
  ∀ (x : X) (U : Set X), IsOpen U → x ∈ U →
    ∃ f : X → ℝ, PX.IsScSmoothMap realPolyfold f ∧ f ≠ 0 ∧ tsupport f ⊆ U

/-- Not the item: the reading of Definition 5.9 with `f ≠ 0` taken as `f(x) ≠ 0`. -/
def AdmitsBumpPointB (PX : MPolyfold X) : Prop :=
  ∀ (x : X) (U : Set X), IsOpen U → x ∈ U →
    ∃ f : X → ℝ, PX.IsScSmoothMap realPolyfold f ∧ f x ≠ 0 ∧ tsupport f ⊆ U

end

/-- Definitions 5.9 and 5.29: the project's (weak) sc-smooth bump function property is the
text's. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X),
    PX.AdmitsBumpFunctionsWeak ↔ AdmitsBumpB PX

/-- Not the item: the project's `AdmitsBumpFunctions` is the pointwise reading. -/
def BPointwise : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X),
    PX.AdmitsBumpFunctions ↔ AdmitsBumpPointB PX

end RoundTrip.V5_16
