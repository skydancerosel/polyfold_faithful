import Polyfold.Chapter2.SubMPolyfoldTangent
import Polyfold.Chapter7.SubGroupoid

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §7.1, the facts (1)–(4)
on a sub-M-polyfold `A` recalled after Definition 7.1.21, pp. 305–307 (2017: Definition 7.10 and
pp. 237–238): the tangent facts (3) and (4).

# The tangent facts (3), (4) for the object set `A` of an ep-subgroupoid

## The text, paraphrased

(2021 pp. 305–307) From Proposition 2.3.19 the object set `A` of an ep-subgroupoid has an induced
M-polyfold structure with (1) `i : A → X` sc-smooth and a topological embedding, (2) `i⁻¹ ∘ r`
sc-smooth for every retraction `r : V → V` onto `A ∩ V`, (3) at a smooth `a ∈ A` the tangent
space `T_aA` has an sc-complement in `T_aX`, (4) for a retraction `r : W → W` onto `A ∩ W` the
induced map `W → A` is sc-smooth and `T_aA = (Tr)(a)T_aX` at a smooth `a ∈ A`.

## What is formalized (row V7.30 of `Exposition/cmp/ch07.json`)

(1), (2) are `isScSmoothMap_val_subObj`, `isScSmoothOn_retractInto_subObj`
(`SubGroupoid.lean`).  Added here, from `Chapter2/SubMPolyfoldTangent.lean`
(Proposition 2.3.19 (3), (4) in `T_aX`):

* `EpGroupoid.subObjInclusionCLM hA hax : T_aA →L[ℝ] T_aX` and
  `EpGroupoid.subObjRetractionCLM hA hax d a₀ hxV : T_aX →L[ℝ] T_aA`, the tangents of `i` and
  of `i⁻¹ ∘ r`.
* **`EpGroupoid.fact_3_subObj_2021`**: `Ti(T_aA)` is a closed subspace of `T_aX` with the closed
  complement `ker T(i⁻¹ ∘ r)` (the linear content of (3)).
* **`EpGroupoid.fact_4_subObj_2021`**: `T(i⁻¹ ∘ r)` is onto `T_aA`, `Ti ∘ T(i⁻¹ ∘ r) = Tr(a)`
  and `Tr(a)T_aX = Ti(T_aA)` (fact (4)).

As in Part I the statements hold for every `a ∈ A₁ ∩ V`; smoothness is not needed.  The
**sc**-complement of (3) is the chart statement `proposition_2_21_3` (`Metrizable.lean`), see
`SubMPolyfoldTangent.lean`.
-/

open Set Function Topology

noncomputable section

namespace Polyfold

namespace EpGroupoid

universe u

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {A : Set Obj} (hA : X.IsEpSubgroupoid A) [ParacompactSpace A]
  {a : (subObjPolyfold hA).Level 1} {x : X.PObj.Level 1}
  (hax : ((subObjPolyfold hA).levelVal 1 a : A).1 = X.PObj.levelVal 1 x)

/-- `Ti : T_aA →L[ℝ] T_aX` for the object set of an ep-subgroupoid. -/
abbrev subObjInclusionCLM : (subObjPolyfold hA).tangentFiber a →L[ℝ] X.PObj.tangentFiber x :=
  MPolyfold.subInclusionCLM hA.isSubMPolyfold hax

variable (d : X.PObj.SubData A) (a₀ : A) (hxV : X.PObj.levelVal 1 x ∈ d.V)

/-- `T(i⁻¹ ∘ r) : T_aX →L[ℝ] T_aA` for the object set of an ep-subgroupoid. -/
abbrev subObjRetractionCLM : X.PObj.tangentFiber x →L[ℝ] (subObjPolyfold hA).tangentFiber a :=
  MPolyfold.subRetractionCLM hA.isSubMPolyfold hax d a₀ hxV

/-- **Fact (3) for `A` (2021 pp. 305–307; 2017 pp. 237–238), the linear content**: `Ti(T_aA)` is
a closed subspace of `T_aX` with the closed complement `ker T(i⁻¹ ∘ r)`, for `a ∈ A₁ ∩ V`. -/
theorem fact_3_subObj_2021 :
    IsClosed (LinearMap.range (subObjInclusionCLM hA hax :
        (subObjPolyfold hA).tangentFiber a →ₗ[ℝ] X.PObj.tangentFiber x) :
          Set (X.PObj.tangentFiber x)) ∧
      IsClosed (LinearMap.ker (subObjRetractionCLM hA hax d a₀ hxV :
        X.PObj.tangentFiber x →ₗ[ℝ] (subObjPolyfold hA).tangentFiber a) :
          Set (X.PObj.tangentFiber x)) ∧
      IsCompl
        (LinearMap.range (subObjInclusionCLM hA hax :
          (subObjPolyfold hA).tangentFiber a →ₗ[ℝ] X.PObj.tangentFiber x))
        (LinearMap.ker (subObjRetractionCLM hA hax d a₀ hxV :
          X.PObj.tangentFiber x →ₗ[ℝ] (subObjPolyfold hA).tangentFiber a)) :=
  MPolyfold.proposition_2_3_19_3_linear_2021 hA.isSubMPolyfold hax d a₀ hxV

/-- **Fact (4) for `A` (2021 pp. 305–307; 2017 pp. 237–238)**: the induced map `i⁻¹ ∘ r : V → A`
is sc-smooth (`isScSmoothOn_retractInto_subObj`), its tangent `T_aX → T_aA` is onto,
`Ti ∘ T(i⁻¹ ∘ r) = Tr(a)` on `T_aX`, and `Tr(a)T_aX = Ti(T_aA)`, i.e. `T_aA = (Tr)(a)T_aX`. -/
theorem fact_4_subObj_2021 :
    Surjective (subObjRetractionCLM hA hax d a₀ hxV) ∧
      (∀ α : X.PObj.tangentFiber x,
        (subObjInclusionCLM hA hax (subObjRetractionCLM hA hax d a₀ hxV α) :
          X.PObj.TangentSpace) = MPolyfold.tangentMapOn d.isScSmoothOn α.1) ∧
      LinearMap.range (((subObjInclusionCLM hA hax).comp (subObjRetractionCLM hA hax d a₀ hxV) :
          X.PObj.tangentFiber x →L[ℝ] X.PObj.tangentFiber x) :
            X.PObj.tangentFiber x →ₗ[ℝ] X.PObj.tangentFiber x) =
        LinearMap.range (subObjInclusionCLM hA hax :
          (subObjPolyfold hA).tangentFiber a →ₗ[ℝ] X.PObj.tangentFiber x) :=
  MPolyfold.proposition_2_3_19_4_2021 hA.isSubMPolyfold hax d a₀ hxV

end EpGroupoid

end Polyfold
