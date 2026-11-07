import Polyfold
/-! Blind formalization of V7_49 (the 2017 book's Part II, §7.3, Definition 7.14, p. 247:
component compact sets).

Text: for an ep-groupoid `X`, a subset `K ⊆ |X|` is component compact if its intersection with
every connected component of `|X|` is compact.

Choices:
- This item is a definition.  B says that the project's `X.IsComponentCompact K` is the text's
  notion `IsComponentCompactB X K` written below.
- Setting: `Obj Mor : Type` (universe 0, as in the other blind files; the project's `EpGroupoid`
  is universe-polymorphic with `Obj`, `Mor` in one universe), with the instances the project's
  `EpGroupoid` asks for (Hausdorff, paracompact object and morphism spaces), and
  `X : EpGroupoid Obj Mor` — the project's ep-groupoid (Definition 7.3; fields read with
  `#print`: a groupoid structure with M-polyfold structures `PObj`, `PMor`, `s, t` local
  sc-diffeomorphisms, `u, ι` sc-smooth, the local properness (3) and sc-smooth `m` (4)).  I did not
  re-derive Definition 7.3; I use the project's structure for "ep-groupoid" throughout Chapter 7.
- `|X|`: the project's `X.OrbitSpace` (checked with `#print`: the quotient of `Obj` by "there is a
  morphism `x → y`"), with Mathlib's quotient topology (`instTopologicalSpaceQuotient`, checked
  with `#synth`).
- "connected component of `|X|`": a set of the form `connectedComponent z`, `z ∈ |X|` (Mathlib);
  "compact": Mathlib's `IsCompact` of the subset `K ∩ C` of `|X|`.
- Nothing looks false to me.
-/
namespace RoundTrip.V7_49
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- **Definition 7.14**: `K ⊆ |X|` meets every connected component of `|X|` in a compact set. -/
def IsComponentCompactB (X : EpGroupoid Obj Mor) (K : Set X.OrbitSpace) : Prop :=
  ∀ C : Set X.OrbitSpace, (∃ z : X.OrbitSpace, connectedComponent z = C) → IsCompact (K ∩ C)

end

/-- Definition 7.14: the project's component compact sets are the text's. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (K : Set X.OrbitSpace),
    X.IsComponentCompact K ↔ IsComponentCompactB X K

end RoundTrip.V7_49
