import Polyfold
/-! Blind formalization of V2_59 (the text's §2.5, Definition 2.52, p. 53).

Text: a section of the strong bundle `P : Y → X` is a map `f : X → Y` with `P ∘ f = 1_X`; it is
sc-smooth if it is sc-smooth as a map into `Y[0]`, and an sc⁺-section if it is sc-smooth as a map
into `Y[1]`.

Choices:
- This item is a definition (three notions), no further property.  B says the project's
  `IsSection`, `StrongBundle.IsScSmoothSection` and `StrongBundle.IsScPlusSection` are equivalent
  to my definitions of the text's notions.
- Setting (as in my `RoundTrip/Blind/V2_58.lean`): `X Y : Type` (universe 0; the project's
  notions are universe-polymorphic), `X` an M-polyfold (`PX : MPolyfold X`), `Y` Hausdorff
  paracompact, fibre linear structures as instances, `Bd : StrongBundle PX P` (Definition 2.51,
  checked in V2_58).  Plain sections make sense for any map `P`; B states them in the text's
  setting of a strong bundle.
- "Section": `P ∘ f = id` (my `IsSectionB`).
- `Y[0]`: the project's `Bd.toMPolyfold0` (checked with `#print`: the M-polyfold on `Y` whose atlas
  is the strong bundle charts `Φ : P⁻¹(V) → K` with models `(K, C ◁ F, E ◁ F)`).  "sc-smooth into
  `Y[0]`": `PX.IsScSmoothMap Bd.toMPolyfold0 f` (Definition 2.14).
- `Y[1]`: the project's `Bd.One` (the subtype `Y_{0,1}`) with `Bd.toMPolyfold1` (checked with
  `#print`: the charts `Φ[1] : P⁻¹(V)[1] → K[1]`; its topology is forced by these charts, see
  V2_58).  "sc-smooth into `Y[1]`": `f` takes values in `Y[1]` and its corestriction is
  sc-smooth: some `g : X → Y[1]` with `oneVal ∘ g = f` (unique, `oneVal` being the inclusion) has
  `PX.IsScSmoothMap Bd.toMPolyfold1 g`.  This is the M-polyfold notion; the project's
  `IsScPlusSection` is phrased in the strong bundle charts, so the third equivalence is a claim.
- Nothing looks false to me.
-/
namespace RoundTrip.V2_59
open Polyfold

/-- **Definition 2.52**: `f : X → Y` is a section of `P : Y → X`: `P ∘ f = 1_X`. -/
def IsSectionB {X Y : Type} (P : Y → X) (f : X → Y) : Prop :=
  P ∘ f = id

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] [T2Space Y] [ParacompactSpace Y]

/-- **Definition 2.52**: an sc-smooth section: a section which is sc-smooth as a map `X → Y[0]`. -/
def IsScSmoothSectionB (Bd : StrongBundle PX P) (f : X → Y) : Prop :=
  IsSectionB P f ∧ PX.IsScSmoothMap Bd.toMPolyfold0 f

/-- **Definition 2.52**: an sc⁺-section: a section with values in `Y[1]` which is sc-smooth as a
map `X → Y[1]`. -/
def IsScPlusSectionB (Bd : StrongBundle PX P) (f : X → Y) : Prop :=
  IsSectionB P f ∧
    ∃ g : X → Bd.One, (∀ x, Bd.oneVal (g x) = f x) ∧ PX.IsScSmoothMap Bd.toMPolyfold1 g

end

/-- Definition 2.52: the project's sections, sc-smooth sections and sc⁺-sections of a strong
bundle are the text's. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] [T2Space Y] [ParacompactSpace Y]
    (Bd : StrongBundle PX P) (f : X → Y),
    (IsSection P f ↔ IsSectionB P f) ∧
    (Bd.IsScSmoothSection f ↔ IsScSmoothSectionB Bd f) ∧
    (Bd.IsScPlusSection f ↔ IsScPlusSectionB Bd f)

end RoundTrip.V2_59
