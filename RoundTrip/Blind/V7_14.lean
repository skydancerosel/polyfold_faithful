import Polyfold
/-! Blind formalization of V7_14 (the 2017 book, Part II, §7.1, Lemma 7.1, p. 230: only finitely
many morphisms from `x` into `U(x₀)`). Choices:
- Setting: `Obj Mor : Type` (universe 0, as in the other blind files) with their topologies
  (`T2`, paracompact) as instances and `X : EpGroupoid Obj Mor` (the project's Definition 7.3,
  fields read with `#print`). The lemma sits in §7.1 about an ep-groupoid `X`, so that is the
  setting; `x, x₀ ∈ X` are objects, `ψ` ranges over the morphism set `𝐗 = Mor`.
- "`U(x₀)` an open neighbourhood of `x₀`": `IsOpen U ∧ x₀ ∈ U`.
- "`t : s⁻¹(cl_X(U(x₀))) → X` is proper": Mathlib's `IsProperMap` of the restriction
  `(s⁻¹(closure U)).domRestrict t`, the domain with the subspace topology of `Mor`. This is the
  same notion as in the properness axiom of the project's `EpGroupoid`. (If the text's "proper"
  means "continuous with compact preimages of compact sets", the two agree here, `X` being
  metrizable and hence compactly generated Hausdorff — Mathlib's
  `isProperMap_iff_isCompact_preimage`.)
- Conclusion: the set `{ψ | s ψ = x ∧ t ψ ∈ U}` is finite (`Set.Finite`), literally as quoted
  (source `x`, target in `U(x₀)`; via `ψ ↦ ψ⁻¹` this is the set of morphisms with target `x` and
  source in `U(x₀)`, so the statement is true as printed).
-/
namespace RoundTrip.V7_14
open Polyfold Topology

/-- Lemma 7.1: if `U` is an open neighbourhood of `x₀` with `t : s⁻¹(cl U) → X` proper, then for
every object `x` only finitely many morphisms `ψ` have `s ψ = x` and `t ψ ∈ U`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (x x₀ : Obj) (U : Set Obj),
    IsOpen U → x₀ ∈ U → IsProperMap ((X.src ⁻¹' closure U).domRestrict X.tgt) →
    {ψ : Mor | X.src ψ = x ∧ X.tgt ψ ∈ U}.Finite

end RoundTrip.V7_14
