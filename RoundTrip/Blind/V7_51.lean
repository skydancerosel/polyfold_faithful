import Polyfold
/-! Blind formalization of V7_51 (the 2017 book's Part II, §7.3, Corollary 7.2, p. 247).

Text: for an ep-groupoid `(X, 𝐗)` and a component compact `K ⊆ |X|` there is an open
neighbourhood `U` of `K` with `cl_{|X|}(U)` paracompact; since `cl_{|X|}(U)` is regular Hausdorff
and locally metrizable, `cl_{|X|}(U)` is metrizable, and therefore `U` is metrizable.

Choices:
- Setting as in `RoundTrip/Blind/V7_49.lean`: `Obj Mor : Type` (universe 0) with the instances
  of the project's `EpGroupoid`, `X : EpGroupoid Obj Mor` (the project's ep-groupoid,
  Definition 7.3, fields read with `#print`); `|X|` the project's `X.OrbitSpace` (the quotient by
  "isomorphic", checked) with the quotient topology.  No hypothesis beyond "ep-groupoid" (no
  paracompact orbit space, no tameness), as in the text.
- "component compact" (Definition 7.14): my `IsComponentCompactB`, copied from V7_49 (every
  connected component `C` of `|X|` has `K ∩ C` compact).
- "open neighbourhood `U` of `K`": `U` open in `|X|` with `K ⊆ U`.  `cl_{|X|}(U)`: Mathlib's
  `closure U` in `|X|`, as a subspace (subtype topology).  "paracompact": Mathlib's
  `ParacompactSpace` (every open cover has a locally finite open refinement; no Hausdorff
  condition — the book's definition, p. 249).  "metrizable": Mathlib's
  `TopologicalSpace.MetrizableSpace` of the subspaces `cl(U)` and `U`.
- B is the conjunction of the claims for ONE `U`: open, `K ⊆ U`, `cl(U)` paracompact, `cl(U)`
  metrizable, `U` metrizable.  The reason given ("`cl(U)` is regular Hausdorff and locally
  metrizable") is not a separate conjunct: it follows from the metrizability of `cl(U)`.
- Nothing looks false to me.
-/
namespace RoundTrip.V7_51
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- **Definition 7.14**: `K ⊆ |X|` meets every connected component of `|X|` in a compact set. -/
def IsComponentCompactB (X : EpGroupoid Obj Mor) (K : Set X.OrbitSpace) : Prop :=
  ∀ C : Set X.OrbitSpace, (∃ z : X.OrbitSpace, connectedComponent z = C) → IsCompact (K ∩ C)

end

/-- Corollary 7.2: a component compact `K ⊆ |X|` has an open neighbourhood `U` with paracompact
(hence metrizable) closure; `U` is metrizable. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (K : Set X.OrbitSpace), IsComponentCompactB X K →
    ∃ U : Set X.OrbitSpace, IsOpen U ∧ K ⊆ U ∧
      ParacompactSpace ↥(closure U) ∧
      TopologicalSpace.MetrizableSpace ↥(closure U) ∧
      TopologicalSpace.MetrizableSpace ↥U

end RoundTrip.V7_51
