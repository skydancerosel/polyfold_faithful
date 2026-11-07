import Polyfold
/-! Blind formalization of V7_29 (the 2017 book, arXiv 1707.08941, Part II, §7.1,
Definition 7.10, p. 237: ep-subgroupoids).

Text: an ep-subgroupoid `A` of the ep-groupoid `X` is the full subcategory associated with a
subset `A ⊆ X` such that (1) `A` is a sub-M-polyfold of the object space `X` and (2) `A` is
saturated, `π⁻¹(π(A)) = A`.

Choices:
- This item is a definition (a property of the subset `A` of objects; the full subcategory is
  then determined).  B says that the project's `X.IsEpSubgroupoid A` is the text's notion.
- Setting: `Obj Mor : Type` (universe 0, as in the other blind files), the project's
  `X : EpGroupoid Obj Mor` (Definition 7.3, `#print`ed), `A : Set Obj`.
- (1) "sub-M-polyfold of the object space": the project's `X.PObj.IsSubMPolyfold A`
  (Definition 2.20 of Part I; its docstring matches, and the earlier blind statement
  `RoundTrip/Blind/V2_23.lean` compares it with the text's definition).
- (2) "saturated": written out with the project's quotient map `π = X.π : X → |X|` (`#print`ed:
  `x ↦ ⟦x⟧`, `|X| = X/∼`, `x ∼ y` iff there is a morphism `x → y`): `π⁻¹(π(A)) = A`.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V7_29
open Polyfold

/-- Definition 7.10: the project's ep-subgroupoids are the saturated sub-M-polyfolds of the object
space. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (A : Set Obj),
    X.IsEpSubgroupoid A ↔ (X.PObj.IsSubMPolyfold A ∧ X.π ⁻¹' (X.π '' A) = A)

end RoundTrip.V7_29
