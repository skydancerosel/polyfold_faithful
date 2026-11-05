import Polyfold
/-! Blind formalization of V5_7 (the text's §5.2, Definition 5.4, p. 171).

Text: (1) `f⁻¹(0)` compact; (2) weakly proper: moreover for every `N` an open `U ⊇ f⁻¹(0)` with
`{f = s}` compact for every sc⁺-section `s` supported in `U` with `N(s) ≤ 1`; (3) proper: moreover
`cl_{X₀}{x ∈ U | N(f(x)) ≤ 1}` compact, `N(f(x)) = ∞` off `Y_{0,1}`.  "Obviously proper implies
weakly proper, which in turn implies compactness."

Choices:
- This item is a definition plus a property.  B says: the project's `Bd.IsWeaklyProper` and
  `Bd.IsProper` (Definition 5.4) are the text's notions `IsWeaklyProperB`, `IsProperB` written
  below, and the text's claim "proper ⇒ weakly proper ⇒ compact solution set" holds.
- Setting: `X Y : Type` (universe 0, as asked); `PX : MPolyfold X`, `P : Y → X` with the
  fibrewise linear structure as instances on the fibres, `Bd : StrongBundle PX P` (Definition
  2.51), as in `RoundTrip/Blind/V5_10.lean`.  No tameness.
- The definitions are stated for every map `f : X → Y` (the project's predicates take any `f`).
- "for every `N`": every auxiliary norm, the project's `Bd.IsAuxNorm N`, `N : Y_{0,1} → ℝ`
  (`Bd.One`) (Definition 5.1, checked with `#print`; compared with the text in
  `RoundTrip/Blind/V5_3.lean`).
- `f⁻¹(0) = {x | f(x) = 0_x}`, `0_x` the zero of the fibre `P⁻¹(x)`; compact in `X = X₀`.
- `N(y) ≤ r` for `y ∈ Y`: `y ∈ Y_{0,1}` and `N(y) ≤ r` (`NLe`; this is "`N = ∞` off `Y_{0,1}`").
  `N(s) ≤ 1`: `N(s(y)) ≤ 1` for all `y ∈ X`.
- "sc⁺-section": `Bd.IsScPlusSection s` (Definition 2.52, checked with `#print`).  "supported in
  `U`": `supp(s) = cl{x | s(x) ≠ 0_x} ⊆ U`.  `{f = s} = {x ∈ X | f(x) = s(x)}`.
- "moreover" in (2) and (3): in addition to (1) (compact solution set).  In (3), `U` is again an
  open neighbourhood of `f⁻¹(0)`, depending on `N`; `cl_{X₀}` is the closure in `X`.
- The property: "proper ⇒ weakly proper" needs `f` continuous (for `{f = s}` to be closed); the
  text's sections are sc-smooth, so I state it for sc-smooth sections `f`
  (`Bd.IsScSmoothSection f`, Definition 2.52, project's, checked) — a presupposition, recorded
  here.  "weakly proper ⇒ compact solution set" is stated for every `f`.
- Nothing looks false to me.
-/
namespace RoundTrip.V5_7
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- The zero `0_x` of the fibre over `x`, as a point of `Y`. -/
def zeroAt (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] (x : X) : Y :=
  ((0 : P ⁻¹' {x}) : Y)

/-- The solution set `f⁻¹(0) = {x | f(x) = 0_x}`. -/
def solSetB (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] (f : X → Y) : Set X :=
  {x | f x = zeroAt P x}

/-- `N(y) ≤ r`, with `N(y) = ∞` for `y ∉ Y_{0,1}`. -/
def NLe (Bd : StrongBundle PX P) (N : Bd.One → ℝ) (y : Y) (r : ℝ) : Prop :=
  ∃ hy : y ∈ Bd.oneSet, N ⟨y, hy⟩ ≤ r

/-- The support `cl{x | s(x) ≠ 0_x}` of a section. -/
def suppB (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] (s : X → Y) : Set X :=
  closure {x | s x ≠ zeroAt P x}

/-- **Definition 5.4 (1)**: `f` has a compact solution set. -/
def HasCompactSolSetB (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] (f : X → Y) : Prop :=
  IsCompact (solSetB P f)

/-- **Definition 5.4 (2)**: `f` is weakly proper. -/
def IsWeaklyProperB (Bd : StrongBundle PX P) (f : X → Y) : Prop :=
  HasCompactSolSetB P f ∧
    ∀ N : Bd.One → ℝ, Bd.IsAuxNorm N →
      ∃ U : Set X, IsOpen U ∧ solSetB P f ⊆ U ∧
        ∀ s : X → Y, Bd.IsScPlusSection s → suppB P s ⊆ U → (∀ y : X, NLe Bd N (s y) 1) →
          IsCompact {x | f x = s x}

/-- **Definition 5.4 (3)**: `f` is proper. -/
def IsProperB (Bd : StrongBundle PX P) (f : X → Y) : Prop :=
  HasCompactSolSetB P f ∧
    ∀ N : Bd.One → ℝ, Bd.IsAuxNorm N →
      ∃ U : Set X, IsOpen U ∧ solSetB P f ⊆ U ∧
        IsCompact (closure {x | x ∈ U ∧ NLe Bd N (f x) 1})

end

/-- Definition 5.4: the project's weakly proper / proper sections are the text's, and (for
sc-smooth sections) proper ⇒ weakly proper ⇒ compact solution set. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P),
    -- the definitions
    (∀ f : X → Y, Bd.IsWeaklyProper f ↔ IsWeaklyProperB Bd f) ∧
    (∀ f : X → Y, Bd.IsProper f ↔ IsProperB Bd f) ∧
    -- "obviously proper implies weakly proper, which in turn implies compactness"
    (∀ f : X → Y, Bd.IsScSmoothSection f → IsProperB Bd f → IsWeaklyProperB Bd f) ∧
    (∀ f : X → Y, IsWeaklyProperB Bd f → HasCompactSolSetB P f)

end RoundTrip.V5_7
