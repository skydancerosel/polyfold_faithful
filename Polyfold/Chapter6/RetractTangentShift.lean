import Polyfold.Chapter2.TangentLift
import Polyfold.Chapter4.ScPlus

/-!
# Tangent maps of shift inclusions

The tangent map of the level inclusion and of the shift inclusion of a retract. The tangent
submanifold results are in `Chapter9/TangentSubmanifoldSmooth.lean`.
-/

set_option maxSynthPendingDepth 3
open Set Function Topology
noncomputable section
namespace Polyfold
universe u

/-- **The tangent of the inclusion `ι : O¹ → O` is `ι : T(O¹) → TO`** (`T(O¹) = (TO)¹`,
`retractTangent_shift_of_isScRetract`): for a retract `O = r(U)` and `a ∈ T(O¹)`,
`Tι(a) = ι a`.  By the chain rule `T(ι ∘ r¹)(a) = Tι(Tr¹(a)) = Tι(a)`, and `Tι` is `ι` on
`TE¹` (the derivative of an sc-operator is itself, `ScOperator.scDeriv_eq`). -/
theorem retractTangentMap_shiftIncl {E : ScBanach} {C : Set (E 0)} (R : ScRetraction E C)
    {a : E.shift.tangent 0}
    (ha : a ∈ retractTangent E.shift (E.lvlSet C 1) (E.lvlSet R.retract 1)) :
    retractTangentMap E.shift (E.lvlSet C 1) (E.lvlSet R.retract 1) (E' := E) (E.shiftIncl 0) a =
      E.tangent.toBase 1 a := by
  have hR1 : R.shift.retract = E.lvlSet R.retract 1 := R.shift_retract
  rw [retractTangentMap_eqOn isScSmoothRetractMap_toBase_one R.shift hR1 ha]
  rw [← hR1, retractTangent_eq] at ha
  obtain ⟨haU, hfix⟩ := R.shift.mem_tangent_iff.1 ha
  have hι := (E.shiftIncl.isScSmooth (isScDomain_univ _)).isSc1
  obtain ⟨_, hchain⟩ := theorem_1_3_1' R.shift.isScDomain (isScDomain_univ _) R.shift.isSc1 hι
    (mapsTo_univ _ _)
  rw [hchain haU, Function.comp_apply, hfix, ScBanach.tangent_toBase]
  refine Prod.ext ?_ ?_
  · exact levelMap_eq_of_toBase_eq rfl
  · change scDeriv univ (E.shiftIncl 0) a.1 a.2 = E.toBase 1 a.2
    rw [ScOperator.scDeriv_eq _ (isScDomain_univ _) (mem_univ _)]
    rfl

/-- `retractTangentMap_shiftIncl` for any sc-smooth retract `O`. -/
theorem retractTangentMap_shiftIncl_of_isScRetract {E : ScBanach} {C O : Set (E 0)}
    (hO : IsScRetract E C O) {a : E.shift.tangent 0}
    (ha : a ∈ retractTangent E.shift (E.lvlSet C 1) (E.lvlSet O 1)) :
    retractTangentMap E.shift (E.lvlSet C 1) (E.lvlSet O 1) (E' := E) (E.shiftIncl 0) a =
      E.tangent.toBase 1 a := by
  obtain ⟨R, rfl⟩ := hO
  exact retractTangentMap_shiftIncl R ha

namespace MPolyfold
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **The tangent of the inclusion `ι : X¹ → X` (Remark 4.3) is the natural inclusion
`T(X¹) → TX`** of Proposition 2.3.17 (`tangentLower`).  In a chart `φ` and its level chart
`φ¹` both read as `ι` on `T(O¹) = (TO)¹` (`retractTangentMap_shiftIncl`,
`tangentChartMap_tangentLower`). -/
theorem tangentMap_levelVal_one (β : P.shift.TangentSpace) :
    tangentMap P.remark_4_1_3_levelVal β = tangentLower β := by
  set y : P.Level 1 := P.shift.levelVal 1 (P.shift.tangentProj β) with hy
  obtain ⟨φ, hφ, hx⟩ := P.exists_isChart_mem_source (P.levelVal 1 y)
  have hχ : P.shift.IsChart (levelChart hφ y) := P.shift_isChart hφ y
  have hβχ : β ∈ tangentChartSet (P := P.shift) (levelChart hφ y) := hx
  have hL : tangentLower β ∈ tangentChartSet (P := P) φ := tangentLower_mem_tangentChartSet hx
  have hR : tangentMap P.remark_4_1_3_levelVal β ∈ tangentChartSet (P := P) φ := by
    change P.levelVal 1 (P.tangentProj (tangentMap _ β)) ∈ φ.source
    rw [levelVal_tangentProj_tangentMap]; exact hx
  refine tangentChartMap_injOn hφ hR hL ?_
  rw [tangentChartMap_tangentMap P.remark_4_1_3_levelVal hχ hφ hβχ hx,
    tangentChartMap_tangentLower β hφ hx y]
  have hdom : levelChart hφ y '' TangentPre.fdom (levelChart hφ y) (P.levelVal 1) φ =
      φ.model.E.lvlSet φ.model.O 1 := by
    have hfd : TangentPre.fdom (levelChart hφ y) (P.levelVal 1) φ = (levelChart hφ y).source :=
      inter_eq_left.2 fun z hz => hz
    rw [hfd, MChart.image_source]
    rfl
  rw [hdom]
  have ha := tangentChartMap_mem hχ hβχ
  change tangentChartMap hχ β ∈ retractTangent φ.model.E.shift (φ.model.E.lvlSet φ.model.C 1)
    (φ.model.E.lvlSet φ.model.O 1) at ha
  have heq : EqOn (φ ∘ P.levelVal 1 ∘ (levelChart hφ y).symm) (φ.model.E.shiftIncl 0)
      (φ.model.E.lvlSet φ.model.O 1) := by
    intro z hz
    have hz' : φ.model.E.toBase 1 z ∈ φ.model.O := hz
    change φ (P.levelVal 1 ((levelChart hφ y).symm z)) = φ.model.E.toBase 1 z
    rw [levelChart_symm_apply hφ y hz', φ.apply_symm_apply hz']
  have hO1 : IsScRetract φ.model.E.shift (φ.model.E.lvlSet φ.model.C 1)
      (φ.model.E.lvlSet φ.model.O 1) := φ.model.isScRetract.shift
  refine (retractTangentMap_congr isScSmoothRetractMap_toBase_one hO1 heq.symm ha).symm.trans ?_
  exact retractTangentMap_shiftIncl_of_isScRetract φ.model.isScRetract ha

end MPolyfold
end Polyfold
end
