import Polyfold
/-! Blind formalization of V7_53 (the 2017 book's Part II, §7.4, Definition 7.15, the paragraph
after it, and Remark 7.1, p. 249).

Text: an ep-groupoid has paracompact orbit space if, besides (1)–(4) of Definition 7.3, (5) `|X|`
is paracompact; paracompact = every open covering has a refinement which is a locally finite open
covering (no Hausdorff condition).  It is not known whether (5) follows from (1)–(4); if `X` has
a second countable topology, (1)–(4) imply (5).  Remark 7.1 is historical.

Choices:
- Setting as in `RoundTrip/Blind/V7_49.lean`: `Obj Mor : Type` (universe 0) with the instances
  of the project's `EpGroupoid`, `X : EpGroupoid Obj Mor` (the project's ep-groupoid, i.e.
  (1)–(4) of Definition 7.3, fields read with `#print`); `|X|` the project's `X.OrbitSpace` (the
  quotient by "isomorphic", checked) with the quotient topology.
- "paracompact": my `IsParacompactB`, written from the text's sentence: every open cover
  `(U_i)_{i : ι}` (`ι : Type`) of `|X|` has an open cover `(V_k)_{k : κ}` (`κ : Type`) that is
  locally finite (Mathlib's `LocallyFinite`) and refines it (every `V_k` lies in some `U_i`).  No
  Hausdorff condition, as the text says.  (This is the field of Mathlib's `ParacompactSpace` for
  a space in `Type`.)
- B is the conjunction of
  (1) the definition: the project's `X.HasParacompactOrbitSpace` holds iff `|X|` is paracompact
      in this sense (for an `X` that is already an ep-groupoid, i.e. (1)–(4) hold);
  (2) "if `X` has a second countable topology, (1)–(4) imply (5)": for every ep-groupoid whose
      OBJECT space `X` is second countable (Mathlib's `SecondCountableTopology Obj`; the text's
      `X` is the object M-polyfold — nothing is assumed about the morphism space), `|X|` is
      paracompact.
- Not formalized: "it is presently not known whether (5) follows from (1)–(4)" and Remark 7.1
  (statements about the state of knowledge and the literature, not mathematical claims).
- Nothing looks false to me.
-/
namespace RoundTrip.V7_53
open Polyfold

/-- The text's paracompactness: every open covering has a refinement which is a locally finite
open covering. -/
def IsParacompactB (T : Type) [TopologicalSpace T] : Prop :=
  ∀ (ι : Type) (U : ι → Set T), (∀ i, IsOpen (U i)) → ⋃ i, U i = Set.univ →
    ∃ (κ : Type) (V : κ → Set T), (∀ k, IsOpen (V k)) ∧ ⋃ k, V k = Set.univ ∧
      LocallyFinite V ∧ ∀ k, ∃ i, V k ⊆ U i

/-- Definition 7.15 (with property (5), `|X|` paracompact), and: a second countable object space
implies (5). -/
def B : Prop :=
  (∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor),
    X.HasParacompactOrbitSpace ↔ IsParacompactB X.OrbitSpace) ∧
  (∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor), SecondCountableTopology Obj →
    IsParacompactB X.OrbitSpace)

end RoundTrip.V7_53
