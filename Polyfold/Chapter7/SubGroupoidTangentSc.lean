import Polyfold.Chapter2.SubMPolyfoldTangentSc
import Polyfold.Chapter7.SubGroupoidTangent

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §7.1, fact (3) on the
object set `A` of an ep-subgroupoid, pp. 305–307 (2017: pp. 237–238): at a smooth `a ∈ A`, `T_aA`
has an sc-complement in `T_aX`.

# The sc-complement of `T_aA` in `T_aX` for an ep-subgroupoid (row V7.30, fact (3))

`SubGroupoidTangent.lean` gives the topological direct sum (`fact_3_subObj`); here, from
`Chapter2/SubMPolyfoldTangentSc.lean`, **`EpGroupoid.fact_3_subObj_sc`**: at a smooth `a`,
in a chart `φ` of `X` around `a`, the images under `Tφ(a)` of `Ti(T_aA)` and of
`ker T(i⁻¹ ∘ r)` are sc-subspaces of `E`, complementary on every level in `T_{φ(a)}O`; this is
the sc-splitting `T_aX = T_aA ⊕ ker T(i⁻¹ ∘ r)` of Proposition 2.3.19 (3) (2021 p. 42).
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
  (d : X.PObj.SubData A) (a₀ : A) (hxV : X.PObj.levelVal 1 x ∈ d.V)
  {φ : MChart Obj} (hφ : X.PObj.IsChart φ) (hxφ : X.PObj.levelVal 1 x ∈ φ.source)

/-- **Fact (3) for `A` (2021 pp. 305–307; 2017 pp. 237–238), the sc-complement**: at a smooth
`a ∈ A`, `T_aA` has the sc-complement `ker T(i⁻¹ ∘ r)` in `T_aX`, read in a chart `φ` around `a`
(Proposition 2.3.19 (3), `MPolyfold.proposition_2_3_19_3_sc`). -/
theorem fact_3_subObj_sc (hs : X.PObj.levelVal 1 x ∈ X.PObj.smoothSet) :
    ∃ K N : Submodule ℝ (φ.model.E 0),
      K = (LinearMap.range (subObjInclusionCLM hA hax :
          (subObjPolyfold hA).tangentFiber a →ₗ[ℝ] X.PObj.tangentFiber x)).map
            (MPolyfold.fiberCoord hφ hxφ) ∧
      N = (LinearMap.ker (subObjRetractionCLM hA hax d a₀ hxV :
          X.PObj.tangentFiber x →ₗ[ℝ] (subObjPolyfold hA).tangentFiber a)).map
            (MPolyfold.fiberCoord hφ hxφ) ∧
      φ.model.E.IsScSubspace K ∧ φ.model.E.IsScSubspace N ∧
      (∀ m, Disjoint (φ.model.E.levelSub K m) (φ.model.E.levelSub N m)) ∧
      (∀ m, φ.model.E.levelSub K m ⊔ φ.model.E.levelSub N m =
        φ.model.E.levelSub (MPolyfold.tangentFiberModel hφ hxφ) m) :=
  MPolyfold.proposition_2_3_19_3_sc hA.isSubMPolyfold hax d a₀ hxV hφ hxφ hs

end EpGroupoid

end Polyfold
