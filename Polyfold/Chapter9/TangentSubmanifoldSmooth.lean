import Polyfold.Chapter9.GeneralCorollaries
import Polyfold.Chapter2.TangentLiftAll

/-!
# Definition 9.2.12: the `TMᵢ` are smooth submanifolds of `TX`

HWZ, *Polyfold and Fredholm Theory* (Springer 2021), Definition 9.2.12, p. 418 (2017:
Definition 9.6, p. 306); Definition 4.1.4 / Definition 4.13 (sc⁺-retractions, smooth
finite-dimensional submanifolds); Proposition 2.3.17, p. 42 (`T(X¹) ≡ (TX)¹`).

For a smooth finite-dimensional submanifold `A` of an M-polyfold `X`, with sc⁺-retraction
`s : V → V` onto `A ∩ V`, the tangent map `Ts : TV → TV` is an sc⁺-retraction of the tangent
M-polyfold `TX` with image `TA ∩ TV`.  So `TA` is a smooth finite-dimensional submanifold of
`TX`, and the `TMᵢ` of Definition 9.2.12 are; with the independence of the tangent sums
(`EpGroupoid.hasIndependentTangentSums`), `TΘ` is a branched ep⁺-subgroupoid of `T(X, 𝐗)` as
soon as `|X|` is paracompact.

## The argument

`s` is sc⁺: `g = 1₀¹ ∘ s : V → X¹` is sc-smooth.  Its tangent `Tg : TV → T(X¹)` is sc-smooth,
and `Ts = T(ι ∘ g) = Tι ∘ Tg` for the inclusion `ι : X¹ → X` (Remark 4.3).  The tangent of `ι`
is the natural inclusion `T(X¹) → TX` of Proposition 2.3.17 (`tangentMap_levelVal_one`; in a
chart it is the sc-operator `E¹ → E`, whose tangent is `TE¹ → TE`,
`retractTangentMap_shiftIncl`).  Hence `Ts(TV)` lies in `(TX)₁`, and `1₀¹ ∘ Ts = Φ ∘ Tg` with the
sc-diffeomorphism `Φ : T(X¹) → (TX)¹` (`tangentShiftMap_isScSmooth`), which is sc-smooth.

## Main results

* `retractTangentMap_shiftIncl`, `MPolyfold.tangentMap_levelVal_one`: `T(ι) = ι_T`.
* `MPolyfold.SubmanifoldData.isScPlusRetractionOn_tmap`: `Ts` is an sc⁺-retraction of `TX`.
* `MPolyfold.IsSmoothSubmanifold.isSmoothSubmanifold_tangent`: `TA` is a smooth
  finite-dimensional submanifold of `TX` (gap G.99).
* `EpGroupoid.tangentBranchingHyp`, `EpGroupoid.isBranchedEpSubgroupoid_tangentTheta_general`:
  Definition 9.2.12 for every branched ep⁺-subgroupoid of an ep-groupoid with paracompact `|X|`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

/-! ### The tangent of the inclusion `E¹ → E` on a retract -/

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

/-! ### `T(ι) = ι_T` for the inclusion `ι : X¹ → X` -/

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

/-! ### `Ts` is an sc⁺-retraction of `TX` -/

namespace SubmanifoldData

variable {A : Set X} (d : P.SubmanifoldData A)

/-- **`Ts = ι_T ∘ T(1₀¹ ∘ s)` on `TV`**: the tangent of the sc⁺-retraction factors through the
natural inclusion `T(X¹) → TX` (`tangentMap_levelVal_one` and the chain rule). -/
theorem tangentLower_tangentMapOn_one (x₀ : P.Level 1) {α : P.TangentSpace}
    (hα : α ∈ P.tangentPreimage d.V) :
    tangentLower (tangentMapOn (d.isScPlusRetractionOn.isScSmoothOn_one x₀) α) = d.tmap α := by
  have hg := d.isScPlusRetractionOn.isScSmoothOn_one x₀
  have hι : P.shift.IsScSmoothOn P (P.levelVal 1) univ := P.remark_4_1_3_levelVal
  have hcomp := tangentMapOn_comp hι hg (mapsTo_univ _ _) hα
  have hcongr := tangentMapOn_congr (hι.comp hg (mapsTo_univ _ _))
    d.isScPlusRetractionOn.isScSmoothOn d.isOpen subset_rfl subset_rfl
    (fun z hz => by
      change P.levelVal 1 (P.toLevelOne x₀ (d.s z)) = d.s z
      exact levelVal_toLevelOne x₀ (d.isScPlusRetractionOn.mem_levelSet z hz)) hα
  rw [hcomp] at hcongr
  rw [Function.comp_apply, tangentMapOn_univ P.remark_4_1_3_levelVal,
    tangentMap_levelVal_one] at hcongr
  exact hcongr

/-- `Ts` maps `TV` into `(TX)₁`. -/
theorem tmap_mem_levelSet {α : P.TangentSpace} (hα : α ∈ P.tangentPreimage d.V) :
    d.tmap α ∈ P.tangentPolyfold.levelSet 1 := by
  rw [← d.tangentLower_tangentMapOn_one (P.tangentProj α) hα]
  exact tangentLower_mem_levelSet _

/-- **The tangent of an sc⁺-retraction is an sc⁺-retraction** (Definition 4.4 on `TX`): for the
data `s : V → V` of a smooth finite-dimensional submanifold, `Ts : TV → TV` is sc-smooth,
idempotent, maps into `(TX)₁`, and `1₀¹ ∘ Ts = Φ ∘ T(1₀¹ ∘ s)` is sc-smooth into `(TX)¹`
(`tangentShiftMap_isScSmooth`). -/
theorem isScPlusRetractionOn_tmap :
    P.tangentPolyfold.IsScPlusRetractionOn d.tmap (P.tangentPreimage d.V) where
  isScSmoothOn := tangentMapOn_isScSmoothOn d.isScPlusRetractionOn.isScSmoothOn
  mapsTo := d.mapsTo_tmap
  idem := fun _ hα => d.tmap_tmap hα
  mem_levelSet := fun _ hα => d.tmap_mem_levelSet hα
  isScSmoothOn_one := fun β₀ => by
    set x₀ : P.Level 1 := P.tangentProj (P.tangentPolyfold.levelVal 1 β₀)
    have hg := d.isScPlusRetractionOn.isScSmoothOn_one x₀
    have hsm := IsScSmoothOn.comp (tangentShiftMap_isScSmooth (P := P))
      (tangentMapOn_isScSmoothOn hg) (mapsTo_univ _ _)
    refine hsm.congr fun α hα => ?_
    change tangentShiftMap (tangentMapOn hg α) = P.tangentPolyfold.toLevelOne β₀ (d.tmap α)
    rw [← d.tangentLower_tangentMapOn_one x₀ hα, ← levelVal_tangentShiftMap,
      toLevelOne_levelVal]

end SubmanifoldData

/-- **`TA` is a smooth finite-dimensional submanifold of `TX`** (gap G.99; for 2021
Definition 9.2.12, p. 418): near each of its points it is the image `Ts(TV) = TA ∩ TV` of the
sc⁺-retraction `Ts` (`SubmanifoldData.isScPlusRetractionOn_tmap`,
`SubmanifoldData.image_tmap`). -/
theorem IsSmoothSubmanifold.isSmoothSubmanifold_tangent {A : Set X}
    (hA : P.IsSmoothSubmanifold A) :
    P.tangentPolyfold.IsSmoothSubmanifold
      {α | α ∈ P.submanifoldTangent A (P.levelVal 1 (P.tangentProj α))} := by
  intro a ha
  obtain ⟨d, hyd⟩ := isSmoothSubmanifold_iff.1 hA _ (mem_of_mem_submanifoldTangent ha)
  exact ⟨P.tangentPreimage d.V, isOpen_tangentPreimage d.isOpen, hyd, d.tmap,
    d.isScPlusRetractionOn_tmap, d.image_tmap⟩

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ}

/-- **The `TMᵢ` of 2021 Definition 9.2.12, p. 418 (2017: Definition 9.6, p. 306), are smooth
finite-dimensional submanifolds of `TX`**, for every local branching structure of every `Θ`
(`MPolyfold.IsSmoothSubmanifold.isSmoothSubmanifold_tangent`). -/
theorem LocalBranchingStructure.isSmoothSubmanifold_tangentSubmanifold {x : Obj}
    (B : X.LocalBranchingStructure Θ x) (i : B.ι) :
    X.tangentEpGroupoid.PObj.IsSmoothSubmanifold (X.tangentSubmanifold (B.M i)) :=
  (B.isSmoothSubmanifold i).isSmoothSubmanifold_tangent

/-- **`TangentBranchingHyp` holds** whenever `|X|` is paracompact: its field `isSmoothSubmanifold`
is `LocalBranchingStructure.isSmoothSubmanifold_tangentSubmanifold`, the others are
`tangentBranchingHyp_of_isSmoothSubmanifold`. -/
theorem tangentBranchingHyp (hX : X.HasParacompactOrbitSpace) (Θ : Obj → ℚ) :
    X.TangentBranchingHyp Θ :=
  tangentBranchingHyp_of_isSmoothSubmanifold hX fun _ B i =>
    B.isSmoothSubmanifold_tangentSubmanifold i

/-- **2021 Definition 9.2.12, p. 418 (2017: Definition 9.6, p. 306)**: for a branched
ep⁺-subgroupoid `Θ` of an ep-groupoid whose orbit space `|X|` is paracompact, `TΘ` is a branched
ep⁺-subgroupoid of `T(X, 𝐗)`.  The independence of the tangent sums is
`hasIndependentTangentSums` (Theorem 9.2.1), the smoothness of the `TMᵢ` is
`LocalBranchingStructure.isSmoothSubmanifold_tangentSubmanifold`. -/
theorem isBranchedEpSubgroupoid_tangentTheta_general (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hX : X.HasParacompactOrbitSpace) :
    X.tangentEpGroupoid.IsBranchedEpSubgroupoid (X.tangentTheta Θ) :=
  isBranchedEpSubgroupoid_tangentTheta_of_isSmoothSubmanifold hΘ (hasIndependentTangentSums Θ) hX
    fun _ B i => B.isSmoothSubmanifold_tangentSubmanifold i

end EpGroupoid

end Polyfold
