import Polyfold.Examples.Path.PartI_MPolyfold
import Polyfold.Chapter4.LocalStrongBundle
import Polyfold.Chapter3.ParamPerturbationG
import Polyfold.Chapter5.StrongBundleMap
import Polyfold.Examples.OrbifoldSquareInfNorm
import Polyfold.Examples.OrbifoldSquareInfFredholm

/-!
# Strong bundles: examples (rows V2.57, V2.61, V2.64, V3.5, V3.6)

* `cubeChart`: `x ↦ ∛x` is a homeomorphism of `ℝ` onto the retract `ℝ`; `not_isChart_cubeChart`:
  it is not a chart of the M-polyfold `ℝ`, so it is the base of no strong bundle chart of
  `ℝ ◁ ℝ → ℝ` (`strongBundleChart_φ_ne_cubeChart`).
* `pullback_BH_snd`: the pull-back of `H ◁ H → H` along `ℝ × H → H` is a strong bundle, and the
  projection to `H ◁ H` is a strong bundle map.
* `not_mem_oneSet_BH_harm`, `oneSet_BH_props`: `(e, h) ∈ Y[1]` iff `h ∈ H_1`; `Y[1]` is metrizable
  and `Y[1] → Y[0]` is sc-smooth.
* `isScSmoothSectionGerm_idSec`, `not_isScSmoothSectionGerm_idSec_harm`: the section
  `e ↦ (e, e)` of `H ◁ H` is an sc-smooth section germ at `0`, and at no point off `H_∞`.
* `principal_idSec_add_constSec`, `isZeroAt_idSec_add_constSec_iff`: the sum of `e ↦ (e, e)` and
  the constant section `e ↦ (e, b)` has principal part `z ↦ z + b`, and vanishes exactly at `−b`.
-/

open Set Function Topology

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.Path

/-! ### A homeomorphism onto the retract which is not a chart -/

theorem cube_surjective : Surjective fun x : ℝ => x ^ 3 := by
  refine Continuous.surjective (continuous_pow 3) (Filter.tendsto_pow_atTop (by norm_num)) ?_
  have h : (fun x : ℝ => x ^ 3) = fun x => -((-x) ^ 3) := funext fun x => by ring
  rw [h]
  exact Filter.tendsto_neg_atTop_atBot.comp
    ((Filter.tendsto_pow_atTop (by norm_num)).comp Filter.tendsto_neg_atBot_atTop)

/-- `x ↦ x³` as a homeomorphism of `ℝ`. -/
def cubeHomeo : ℝ ≃ₜ ℝ :=
  (StrictMono.orderIsoOfSurjective (fun x : ℝ => x ^ 3) (Odd.strictMono_pow (by decide))
    cube_surjective).toHomeomorph

theorem cubeHomeo_apply (x : ℝ) : cubeHomeo x = x ^ 3 := rfl

/-- The cube root `cubeHomeo.symm` is not differentiable at `0`. -/
theorem not_differentiableAt_cubeRoot : ¬ DifferentiableAt ℝ cubeHomeo.symm 0 := by
  intro h
  have h0 : cubeHomeo.symm 0 = 0 := by
    rw [cubeHomeo.symm_apply_eq, cubeHomeo_apply]; norm_num
  have h1 := h.hasDerivAt.pow 3
  rw [h0] at h1
  have h2 : (cubeHomeo.symm : ℝ → ℝ) ^ 3 = id :=
    funext fun y => (cubeHomeo_apply _).symm.trans (cubeHomeo.apply_symm_apply y)
  rw [h2] at h1
  have := h1.unique (hasDerivAt_id 0)
  norm_num at this

/-- The point `0` of the M-polyfold `ℝ`. -/
def u0 : RU := ⟨0, mem_univ _⟩

/-- The projection `ℝ × ℝ → ℝ` of the trivial strong bundle `ℝ ◁ ℝ → ℝ`. -/
abbrev projR : RU × Rc 0 → RU := LocalBundle.proj (E := Rc) (U := (univ : Set (Rc 0))) (F := Rc)

instance instAddCommGroupProjR (x : RU) : AddCommGroup (projR ⁻¹' {x}) :=
  LocalBundle.instAddCommGroupElemProdLvlOfNatNatPreimageProjSingletonSet x

instance instModuleProjR (x : RU) : Module ℝ (projR ⁻¹' {x}) :=
  LocalBundle.instModuleRealElemProdLvlOfNatNatPreimageProjSingletonSet x

/-- The M-polyfold `ℝ` underlying the trivial strong bundle `ℝ ◁ ℝ → ℝ` (one chart). -/
abbrev RB : MPolyfold RU := LocalBundle.basePolyfold relOpen_univ_Rc u0

/-- The trivial strong bundle `ℝ ◁ ℝ → ℝ`. -/
abbrev BR : StrongBundle RB projR :=
  LocalBundle.bundle Rc relOpen_univ_Rc u0

/-- The homeomorphism `x ↦ ∛x` of `ℝ` onto the retract `ℝ`, as a candidate chart. -/
def cubeChart : MChart RU where
  model := LocalModel.ofRelOpen relOpen_univ_Rc
  toPartialEquiv :=
    { toFun := fun x => cubeHomeo.symm (x : ℝ)
      invFun := fun z => ⟨cubeHomeo z, mem_univ _⟩
      source := univ
      target := univ
      map_source' := fun _ _ => mem_univ _
      map_target' := fun _ _ => mem_univ _
      left_inv' := fun _ _ => Subtype.ext (cubeHomeo.apply_symm_apply _)
      right_inv' := fun z _ => cubeHomeo.symm_apply_apply z }
  isOpen_source := isOpen_univ
  target_eq := rfl
  continuousOn_toFun := (cubeHomeo.symm.continuous.comp continuous_subtype_val).continuousOn
  continuousOn_invFun := (cubeHomeo.continuous.subtype_mk fun _ => mem_univ _).continuousOn

/-- Row V2.57, a non-example for Definition 2.6.4 (pp. 67–68): `x ↦ ∛x` is a homeomorphism of `ℝ`
onto the retract `O = ℝ`, but it is not a chart of the M-polyfold `ℝ` (the transition from the
identity chart is `∛`, not sc-smooth at `0`). -/
theorem not_isChart_cubeChart : ¬ RB.IsChart cubeChart := by
  intro h
  have hc := (h (LocalBundle.baseChart relOpen_univ_Rc u0) (mem_singleton _)).2
  set φ := LocalBundle.baseChart relOpen_univ_Rc u0
  have htr : φ.transition cubeChart = cubeHomeo.symm := by
    funext z
    change cubeHomeo.symm ((φ.symm z : RU) : ℝ) = cubeHomeo.symm z
    rw [show ((φ.symm z : RU) : ℝ) = z from φ.apply_symm_apply (mem_univ z)]
  have hov : φ.overlap cubeChart = univ := by
    refine eq_univ_of_forall fun z => ⟨⟨z, mem_univ z⟩, ⟨mem_univ _, mem_univ _⟩, rfl⟩
  rw [htr, hov] at hc
  have h2 := hc.comp_isScSmooth (ScRetraction.id relOpen_univ_Rc) (image_id _)
  have h3 := (isScSmooth_iff_contDiffOn_const relOpen_univ_Rc.isScDomain _).1 h2
  exact not_differentiableAt_cubeRoot
    ((contDiffOn_univ.1 h3).differentiable (by simp) 0)

/-- Row V2.57, Definition 2.6.4 (pp. 67–68): no strong bundle chart of `ℝ ◁ ℝ → ℝ` has the base
homeomorphism `x ↦ ∛x`, since the base of a strong bundle chart is a chart of the M-polyfold. -/
theorem strongBundleChart_φ_ne_cubeChart
    (c : StrongBundleChart RB projR) :
    c.φ ≠ cubeChart := fun h => not_isChart_cubeChart (h ▸ c.isChart)

/-! ### The strong bundle `H ◁ H → H` -/

section BH

open OrbifoldSquareInf WeightedEllTwo StrongBundle

instance : ParacompactSpace ((Fin 1 → ℝ) × HObj) :=
  MPolyfold.paracompactSpace_prod (rnPolyfold 1) PH

instance : ParacompactSpace (pullbackSpace (LocalBundle.proj (E := H) (U := (univ : Set (H 0)))
    (F := H)) (Prod.snd : (Fin 1 → ℝ) × HObj → HObj)) :=
  paracompactSpace_pullbackSpace ((rnPolyfold 1).prod PH) BH

/-- Row V2.61, Proposition 2.6.8 (p. 69): the pull-back of `H ◁ H → H` along the sc-smooth
projection `ℝ × H → H` is a strong bundle over `ℝ × H` whose atlas consists of the pulled-back
charts, and the projection `(r, e, h) ↦ (e, h)` to `H ◁ H` is a strong bundle map. -/
theorem pullback_BH_snd :
    (∃ B' : StrongBundle ((rnPolyfold 1).prod PH)
        (pullbackProj (LocalBundle.proj (E := H) (U := (univ : Set (H 0))) (F := H)) Prod.snd),
      B'.atlas.charts = (pullbackAtlas BH (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PH)).charts) ∧
    (BH.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PH)).IsStrongBundleMap BH Prod.snd
      (pullbackProj' (LocalBundle.proj (E := H) (U := (univ : Set (H 0))) (F := H)) Prod.snd) :=
  ⟨proposition_2_6_8 BH (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PH),
    BH.isStrongBundleMap_pullbackProj' (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PH)⟩

/-- Row V2.64, a non-example: over every point of `H`, the vector `(1/(k+1))_k` of the fibre `H_0`
is not in `Y[1]`, since it is not in `H_1`. -/
theorem not_mem_oneSet_BH_harm (x : HObj) : ((x, harmH) : HObj × H 0) ∉ BH.oneSet :=
  fun h => let ⟨y, hy⟩ := mem_oneSet_BH.1 h; incl_ne_harm y hy

/-- Row V2.64: for `H ◁ H → H`, the points `(e, 0)` lie in `Y[1]`, `Y[1]` is metrizable, and
the inclusion `Y[1] → Y[0]` is sc-smooth. -/
theorem oneSet_BH_props :
    ((h0, (0 : H 0)) : HObj × H 0) ∈ BH.oneSet ∧ TopologicalSpace.MetrizableSpace BH.One ∧
      BH.toMPolyfold1.IsScSmoothMap BH.toMPolyfold0 BH.oneVal :=
  ⟨zero_mem_oneSet_BH h0, BH.metrizableSpace_one, BH.isScSmoothMap_oneVal⟩

/-- The chart `(e, h) ↦ (e, h)` of `H ◁ H` is compatible with the atlas. -/
theorem isChart_chH : BH.IsChart chH := LocalBundle.isChart_chart relOpen_H h0

/-- Row V3.5, Definition 3.1.3 (p. 91): the section `e ↦ (e, e)` of `H ◁ H → H` is an sc-smooth
section germ at `0`. -/
theorem isScSmoothSectionGerm_idSec : BH.IsScSmoothSectionGerm idSec h0 :=
  isScFredholmSectionTame_idSec.isScSmooth.isScSmoothSectionGerm
    ((LocalBundle.mem_smoothSet_iff relOpen_H h0).2 (Submodule.zero_mem _)) isChart_chH
    (mem_univ _) rfl

/-- Row V3.5, a non-example: `e ↦ (e, e)` is not an sc-smooth section germ at
`(1/(k+1))_k`, which is not a smooth point. -/
theorem not_isScSmoothSectionGerm_idSec_harm : ¬ BH.IsScSmoothSectionGerm idSec (hpt harmH) :=
  fun h => harmH_not_mem_smooth ((LocalBundle.mem_smoothSet_iff relOpen_H h0).1 h.smooth_pt)

theorem principal_sec (k : H 0 → H 0) {z : H 0} :
    chH.principal (LocalBundle.sec (E := H) (U := (univ : Set (H 0))) (F := H) k) z = k z := by
  change k ((chH.φ.symm z : HObj) : H 0) = k z
  rw [show ((chH.φ.symm z : HObj) : H 0) = z from chH.φ.apply_symm_apply (mem_univ z)]

/-- The section `e ↦ (e, k(e))` of `H ◁ H → H`. -/
abbrev secH (k : H 0 → H 0) : HObj → HObj × H 0 :=
  LocalBundle.sec (E := H) (U := (univ : Set (H 0))) (F := H) k

/-- Row V3.6 (p. 98), the sum rule: in the chart `(e, h) ↦ (e, h)`, the fibrewise sum of
`e ↦ (e, e)` and the constant section `e ↦ (e, b)` has principal part `z ↦ z + b`. -/
theorem principal_idSec_add_constSec (b z : H 0) :
    chH.principal
      (sectionAdd (LocalBundle.proj (E := H) (U := (univ : Set (H 0))) (F := H)) (secH id)
        (secH fun _ => b)) z =
      z + b := by
  refine (chH.principal_sectionAdd (f := secH id) (s := secH fun _ => b)
    (LocalBundle.isSection_sec _) (LocalBundle.isSection_sec _) (mem_univ z)).trans ?_
  rw [principal_sec, principal_sec]
  rfl

/-- Row V3.6: the fibrewise sum of `e ↦ (e, e)` and `e ↦ (e, b)` vanishes exactly at `e = −b`. -/
theorem isZeroAt_idSec_add_constSec_iff (b : H 0) (x : HObj) :
    IsZeroAt (LocalBundle.proj (E := H) (U := (univ : Set (H 0))) (F := H))
      (sectionAdd (LocalBundle.proj (E := H) (U := (univ : Set (H 0))) (F := H)) (secH id)
        (secH fun _ => b))
      x ↔ (x : H 0) = -b := by
  refine (chH.isZeroAt_iff (f := sectionAdd _ (secH id) (secH fun _ => b))
    ((LocalBundle.isSection_sec _).sectionAdd (LocalBundle.isSection_sec _)) (mem_univ x)).trans ?_
  have h := principal_idSec_add_constSec b (chH.φ x)
  exact (Eq.congr_left h).trans add_eq_zero_iff_eq_neg

end BH

end Polyfold.Examples.Path
