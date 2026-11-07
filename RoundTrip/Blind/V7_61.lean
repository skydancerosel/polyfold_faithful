import Polyfold
/-! Blind formalization of V7_61 (the 2017 book's Part II, §7.4, Proposition 7.14, p. 251).

Text: let `X` be an ep-groupoid.  (1) If `Q ⊆ X` is proper, then `π(Q)` is closed in `|X|`.
(2) If `|X|` is paracompact, then `A ⊆ |X|` is closed iff there is a proper `Q ⊆ X` with
`π(Q) = A`.

Choices:
- Setting: `Obj Mor : Type` (universe 0, as in the other blind files), with the instances of the
  project's `EpGroupoid`, `X : EpGroupoid Obj Mor` (the project's Definition 7.3, fields read
  with `#print`, as in `RoundTrip/Blind/V7_49.lean`).
- `|X|`: the project's `X.OrbitSpace` (`#print`: the quotient of `Obj` by "there is a morphism
  `x → y`"), with Mathlib's quotient topology (`instTopologicalSpaceQuotient`, `#synth`);
  `π` is the project's `X.π` (`#print`: `x ↦ ⟦x⟧`).
- "proper" (Definition 7.17): the project's `X.IsProperSubset` (`#print`: Mathlib's
  `IsProperMap` of `t : s⁻¹(Q) → X`; its agreement with the classical notion is item V7_59).
- "`|X|` paracompact": Mathlib's `ParacompactSpace X.OrbitSpace` (the project's
  `HasParacompactOrbitSpace` is exactly this, `#print`).  Mathlib's notion does not include
  Hausdorff; if the text's "paracompact" includes it, nothing changes as far as I can see, since
  `|X|` of an ep-groupoid is Hausdorff (by the properness in Definition 7.3 (3)).
- B is the conjunction of (1) and (2), (2) for all `A : Set |X|`.
- Nothing looks false to me.
-/
namespace RoundTrip.V7_61
open Polyfold

/-- Proposition 7.14: images of proper sets are closed in `|X|`; for paracompact `|X|` every
closed set of `|X|` is such an image. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    (∀ Q : Set Obj, X.IsProperSubset Q → IsClosed (X.π '' Q)) ∧
    (ParacompactSpace X.OrbitSpace →
      ∀ A : Set X.OrbitSpace, IsClosed A ↔ ∃ Q : Set Obj, X.IsProperSubset Q ∧ X.π '' Q = A)

end RoundTrip.V7_61
