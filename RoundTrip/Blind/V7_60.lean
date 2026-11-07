import Polyfold
/-! Blind formalization of V7_60 (the 2017 book's Part II, §7.4, Proposition 7.13, p. 251).

Text: if `Q ⊆ X` is proper, then it is a closed subset of `X`.

Choices:
- Setting: `Obj Mor : Type` (universe 0, as in the other blind files), with the instances of the
  project's `EpGroupoid`, `X : EpGroupoid Obj Mor` (the project's Definition 7.3, fields read
  with `#print`, as in `RoundTrip/Blind/V7_49.lean`).
- "`Q` proper" (Definition 7.17): the project's `X.IsProperSubset Q`, read with `#print`:
  Mathlib's `IsProperMap` of `t` restricted to the subspace `s⁻¹(Q)` of `𝐗`, the text's
  definition literally.  (Mathlib's `IsProperMap` is "continuous and universally closed"; on these
  first countable Hausdorff spaces it is the classical "continuous with compact preimages of
  compact sets"; that agreement is item V7_59.)
- "closed subset of `X`": Mathlib's `IsClosed Q` in the object space `Obj`.
- Nothing looks false to me.
-/
namespace RoundTrip.V7_60
open Polyfold

/-- Proposition 7.13: proper subsets of the object space are closed. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (Q : Set Obj), X.IsProperSubset Q → IsClosed Q

end RoundTrip.V7_60
