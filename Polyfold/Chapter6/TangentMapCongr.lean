import Polyfold.Chapter2.TangentMap

/-!
# Congruence of tangent maps

Tangent maps of functions that agree are equal. The tangent ep-groupoid is in
`Chapter8/TangentEp.lean`.
-/

open Set Function Topology Filter CategoryTheory
noncomputable section
namespace Polyfold
universe u v w
namespace MPolyfold
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {S : MPolyfold Z}

/-- Part I's `Tf` depends only on the map `f`. -/
theorem tangentMap_congr_fun {f g : X → Y} (hf : P.IsScSmoothMap Q f) (hg : P.IsScSmoothMap Q g)
    (h : f = g) : tangentMap hf = tangentMap hg := by
  subst h
  rfl

end MPolyfold
end Polyfold
end
