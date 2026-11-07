import Polyfold
/-! Blind formalization of V7_15 (the 2017 book, Part II, §7.1, Proposition 7.4, p. 230: the
isotropy groups are finite). Choices:
- Setting: `Obj Mor : Type` (universe 0, as in the other blind files) with their topologies
  (`T2`, paracompact) as instances and `X : EpGroupoid Obj Mor` (the project's Definition 7.3,
  fields read with `#print`).
- The isotropy group `G_x` (Definition 7.2) is the set of morphisms `x → x`, written out here as
  `{g : Mor | s g = x ∧ t g = x}` rather than through the project's `Isotropy` structure (which
  has exactly these elements: a morphism with the two equations, read with `#print`); its group
  law plays no role in finiteness.
- "`G_x` is finite": `Set.Finite` of that set.
-/
namespace RoundTrip.V7_15
open Polyfold

/-- Proposition 7.4: every isotropy group `G_x` of an ep-groupoid is finite. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (x : Obj), {g : Mor | X.src g = x ∧ X.tgt g = x}.Finite

end RoundTrip.V7_15
