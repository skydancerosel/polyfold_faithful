import Polyfold
/-! Blind formalization of V7_59 (the 2017 book's Part II, §7.4, Definition 7.17, p. 251:
proper subsets and the properness property).

Text: `Q ⊆ X` is proper if `t : s⁻¹(Q) → X` is proper; an open `U ⊆ X` has the properness
property if `cl_X(U)` is proper.

Choices:
- This item is a definition.  B says that the project's `X.IsProperSubset Q` and
  `X.HasPropernessProperty U` are the text's notions, with "proper map" written below from
  Mathlib alone (`IsProperT`), not with Mathlib's `IsProperMap`.
- Setting: `Obj Mor : Type` (universe 0, as in the other blind files; the project's `EpGroupoid`
  has `Obj`, `Mor` in one universe), with the instances of the project's `EpGroupoid`, and
  `X : EpGroupoid Obj Mor` (the project's Definition 7.3, fields read with `#print`, as in
  `RoundTrip/Blind/V7_49.lean`).  `s, t` are `X.src`, `X.tgt`.
- "proper map" (`IsProperT`): the classical notion, continuous with preimages of compact sets
  compact.  The map is `t` restricted to the subspace `s⁻¹(Q)` of `𝐗` (Mathlib's
  `Set.domRestrict`).  The project's definitions (read with `#print`) use Mathlib's `IsProperMap`
  (continuous and universally closed); the two agree when the target is Hausdorff and compactly
  generated, e.g. first countable, which `X` is (locally a retract in a Banach space).  So B is
  true but its proof needs this.
- `cl_X(U)` is `closure U` in `Obj`.  The text defines the properness property for OPEN `U` only;
  B speaks only of open `U` (the project's definition also asks `IsOpen U`).
- Nothing looks false to me.
-/
namespace RoundTrip.V7_59
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- `Q ⊆ X` is proper: `t : s⁻¹(Q) → X` is continuous and preimages of compact sets are
compact. -/
def IsProperT (X : EpGroupoid Obj Mor) (Q : Set Obj) : Prop :=
  Continuous ((X.src ⁻¹' Q).domRestrict X.tgt) ∧
    ∀ K : Set Obj, IsCompact K → IsCompact ((X.src ⁻¹' Q).domRestrict X.tgt ⁻¹' K)

end

/-- Definition 7.17: the project's proper subsets and properness property are the text's. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    (∀ Q : Set Obj, X.IsProperSubset Q ↔ IsProperT X Q) ∧
    ∀ U : Set Obj, IsOpen U → (X.HasPropernessProperty U ↔ IsProperT X (closure U))

end RoundTrip.V7_59
