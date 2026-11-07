import Polyfold
/-! Blind formalization of V7_20 (the 2017 book, Part II, §7.1, p. 232: the M-polyfold
`G × U`). Choices:
- Setting: `Obj Mor : Type` (universe 0, as in the other blind files) with their topologies
  (`T2`, paracompact) as instances and `X : EpGroupoid Obj Mor` (the project's Definition 7.3,
  fields read with `#print`); `PObj` is the M-polyfold structure of the object space `X`.
- `G = G_x` is my type `Gx X x = {g : Mor // s g = x ∧ t g = x}` with the discrete topology
  (a local instance; "the finite group `G`" is a discrete space). The group law is irrelevant.
- `U`: in the text the neighbourhood of Theorem 7.1. The claim only uses that `U` is an open
  subset of `X` (an M-polyfold with the charts of `X` inside `U`), so I state it for every open
  `U` with `x ∈ U`; this is more general than "the `U` of Theorem 7.1" (recorded here).
- `G × U` is the type `Gx X x × ↥U` with the product topology (discrete × subspace), which is the
  topology of the disjoint union of the copies `{g} × U`. Its paracompactness (needed for the
  project's `MPolyfold`) is part of the existential, not an assumption.
- "A natural M-polyfold structure as the finite disjoint union of copies of the M-polyfold `U`":
  an M-polyfold structure `P` on `G × U` such that, for every `g`, the projection
  `(g, y) ↦ y` restricted to the copy `{g} × U` (open in `G × U`) is an sc-diffeomorphism onto
  the open set `U ⊆ X` (`MPolyfold.IsScDiffeoOn P PObj _ ι ({g} ×ˢ univ) U` with some inverse
  `ι`, read with `#print`). This says each copy is the M-polyfold `U`, and it determines the
  structure up to equivalence of atlases. I did not use the project's `discretePolyfold` /
  `MPolyfold.prod` / `NaturalRep.morPolyfold` (the claim is the existence of the structure, not
  a property of the project's construction).
-/
namespace RoundTrip.V7_20
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- The isotropy group `G_x`: the morphisms `x → x`. -/
def Gx (X : EpGroupoid Obj Mor) (x : Obj) : Type := {g : Mor // X.src g = x ∧ X.tgt g = x}

/-- `G_x` as a discrete space. -/
instance instTopGx (X : EpGroupoid Obj Mor) (x : Obj) : TopologicalSpace (Gx X x) := ⊥

instance (X : EpGroupoid Obj Mor) (x : Obj) : DiscreteTopology (Gx X x) := ⟨rfl⟩

end

/-- `G_x × U` (`U ⊆ X` open) is an M-polyfold, the disjoint union of the copies `{g} × U` of the
M-polyfold `U`: on each copy the projection to `U` is an sc-diffeomorphism. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (x : Obj) (U : Set Obj), IsOpen U → x ∈ U →
    ∃ (_ : ParacompactSpace (Gx X x × U)) (P : MPolyfold (Gx X x × U)),
      ∀ g : Gx X x, ∃ ι : Obj → Gx X x × U,
        P.IsScDiffeoOn X.PObj (fun p : Gx X x × U => (p.2 : Obj)) ι
          (({g} : Set (Gx X x)) ×ˢ (Set.univ : Set U)) U

end RoundTrip.V7_20
