import Polyfold
/-! Blind formalization of V7_34 (the 2017 book's Part II, §7.2, Lemma 7.2, p. 239).

Text: for an ep-groupoid `X` the regular part `X_reg` is open.

Choices:
- Setting: `Obj Mor : Type` (spaces in `Type`; the project's `EpGroupoid` is universe-polymorphic,
  this is `u = 0`), with their topologies, Hausdorff and paracompact, `X : EpGroupoid Obj Mor`
  (the project's Definition 7.3, checked with `#print`; see `RoundTrip/Blind/V7_33.lean`).
- `X_reg = {x | G_x = {1_x}}` is my `XregB` (as in `RoundTrip/Blind/V7_33.lean`): `G_x` is the
  project's `X.Isotropy x` (morphisms `g` with `s g = t g = x`), and `G_x = {1_x}` says every such
  `g` is the unit `u(x)`.  I do not use the project's `regularSet` (V7_33 asserts it is mine).
- "open": open in the topology of the object space `Obj`.
- Nothing looks false to me.
-/
namespace RoundTrip.V7_34
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- **Definition 7.11**: `x` is regular: `G_x = {1_x}`. -/
def IsRegularB (X : EpGroupoid Obj Mor) (x : Obj) : Prop :=
  ∀ g : X.Isotropy x, g.val = X.unit x

/-- The regular part `X_reg = {x ∈ X | G_x = {1_x}}`. -/
def XregB (X : EpGroupoid Obj Mor) : Set Obj :=
  {x | IsRegularB X x}

end

/-- Lemma 7.2: the regular part of an ep-groupoid is open. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    IsOpen (XregB X)

end RoundTrip.V7_34
