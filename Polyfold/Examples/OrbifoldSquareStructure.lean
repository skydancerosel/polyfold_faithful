import Polyfold.Examples.OrbifoldSquareBundle
import Polyfold.Chapter16.CircleSectionPolyfold
import Polyfold.Chapter17.BundleModelStructure

/-!
# The orbifold `ℂ/ℤ₅` and the section `z ↦ z²`: the polyfold and the strong polyfold bundle

A worked example for Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021),
Theorem 16.6.6, 2021 p. 739.

## What is formalized (namespace `Polyfold.Examples.OrbifoldSquare`)

* `isEffective_X5` (Definition 7.2.1), `isotropyZeroEquiv` (`G_0 ≅ ℤ/5`),
  `isRegular_X5_iff` (trivial isotropy away from `0`).
* `isZhou_X5` (Definition 7.4.5): the isotropy `ζ^g` of `0` moves a tangent vector at `0`.
* `isLRLocal_E5` (Definition 8.4.2), `hasParacompactOrbitSpace_X5`.
* `sqStructure`, `sqBundle`: the strong polyfold bundle structure and the strong polyfold bundle
  `|ℂ × ℂ| → |ℂ|` over `ℂ/ℤ₅` (Definitions 16.3.1, 16.3.4).
* `sqRep`, `sqFredholmSection`: the sc-Fredholm section `|z| ↦ |(z, z²)|` (Definition 16.6.1).
* `sqBundle_boundary_eq_empty`: `∂Z = ∅`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.OrbifoldSquare

open TrivialBundle EpGroupoid.Examples StrongBundle MPolyfold StrongPolyfoldBundle
  StrongPolyfoldBundleStructure

/-! ### Isotropy -/

/-- A morphism `(k, x)` with `k ≠ 1` and `k · x = x` sits over `x = 0`. -/
theorem eq_zero_of_isotropy {x : Fin 2 → ℝ} (g : X5.Isotropy x) (hg : g ≠ 1) : x = 0 := by
  have h2 : g.val.2 = x := g.src_val
  have ht : g.val.1 • g.val.2 = x := g.tgt_val
  have h1 : g.val.1 ≠ 1 := fun h => hg (GroupoidStr.Isotropy.ext (Prod.ext h h2))
  rw [h2] at ht
  exact (smul_eq_self_iff h1 x).1 ht

/-- **`ℤ/5 ⋉ ℂ` is effective** (Definition 7.2.1): near `(k, 0)`, `k ≠ 1`, there are `(k, y)`
with `y ≠ 0`, and `k · y ≠ y`. -/
theorem isEffective_X5 : X5.IsEffective := by
  intro x g hg W hW hgW
  have h2 : g.val.2 = x := g.src_val
  have h1 : g.val.1 ≠ 1 := fun h => hg (GroupoidStr.Isotropy.ext (Prod.ext h h2))
  have hx : x = 0 := eq_zero_of_isotropy g hg
  have hS : IsOpen {y : Fin 2 → ℝ | (g.val.1, y) ∈ W} :=
    hW.preimage (continuous_const.prodMk continuous_id)
  have hg0 : g.val = (g.val.1, (0 : Fin 2 → ℝ)) := Prod.ext rfl (h2.trans hx)
  have h0S : (0 : Fin 2 → ℝ) ∈ {y : Fin 2 → ℝ | (g.val.1, y) ∈ W} := by
    change (g.val.1, (0 : Fin 2 → ℝ)) ∈ W
    rw [← hg0]
    exact hgW
  have hN : {y : Fin 2 → ℝ | (g.val.1, y) ∈ W} ∈ 𝓝[≠] (0 : Fin 2 → ℝ) :=
    mem_nhdsWithin_of_mem_nhds (hS.mem_nhds h0S)
  obtain ⟨y, hyW, hy0⟩ := Filter.nonempty_of_mem (inter_mem hN self_mem_nhdsWithin)
  refine ⟨(g.val.1, y), hyW, ?_⟩
  change y ≠ g.val.1 • y
  exact fun h => hy0 ((smul_eq_self_iff h1 y).1 h.symm)

/-- `G_0 ≅ ℤ/5`. -/
def isotropyZeroEquiv : X5.Isotropy (0 : Fin 2 → ℝ) ≃* G5 :=
  (isotropyEquivStabilizer isScSmoothMap_smul 0).trans
    ((MulEquiv.subgroupCongr (eq_top_iff.2 fun k _ =>
      MulAction.mem_stabilizer_iff.2 (smul_zero5 k))).trans Subgroup.topEquiv)

/-- An object of `ℤ/5 ⋉ ℂ` has trivial isotropy iff it is not `0`. -/
theorem isRegular_X5_iff {x : Fin 2 → ℝ} : X5.IsRegular x ↔ x ≠ 0 := by
  rw [X5, isRegular_action_iff]
  constructor
  · rintro h rfl
    have := h (Multiplicative.ofAdd 1) (smul_zero5 _)
    exact absurd this (by decide)
  · intro hx k hk
    by_contra hk1
    exact hx ((smul_eq_self_iff hk1 x).1 hk)

/-- Every `T_x` is trivial. -/
theorem trivialSubgroup_X5 (x : Fin 2 → ℝ) : X5.trivialSubgroup x = ⊥ :=
  X5.isEffective_iff_trivialSubgroup_eq_bot.1 isEffective_X5 x

/-! ### (ZHOU) -/

/-- The vector `(0, w)` of `T_0ℂ` in the chart `y ↦ y`. -/
def zeroVec (w : Fin 2 → ℝ) : (rnChart 2 0).model.E.tangent 0 := ((0 : Fin 2 → ℝ), w)

theorem zeroVec_mem (w : Fin 2 → ℝ) :
    zeroVec w ∈ retractTangent (rnChart 2 0).model.E (rnChart 2 0).model.C
      (rnChart 2 0).model.O := by
  change zeroVec w ∈ retractTangent (rnSc 2) univ univ
  rw [retractTangent_univ]
  exact mem_univ _

/-- `[0, y ↦ y, w] ∈ T_0ℂ`. -/
def zeroTangent (w : Fin 2 → ℝ) : (rnPolyfold 2).TangentSpace :=
  TangentSpace.mk (TangentPre.ofVec (isChart_rnChart 0) (zeroVec_mem w))

theorem levelVal_tangentProj_zeroTangent (w : Fin 2 → ℝ) :
    (rnPolyfold 2).levelVal 1 ((rnPolyfold 2).tangentProj (zeroTangent w)) = 0 := by
  change (rnChart 2 0).model.E.toBase 1 0 + 0 = 0
  rw [map_zero, add_zero]

theorem tangentChartMap_zeroTangent (w : Fin 2 → ℝ) :
    tangentChartMap (isChart_rnChart 0) (zeroTangent w) = zeroVec w :=
  tangentChartMap_mk_ofVec _ (zeroVec_mem w)

/-- `T(g ·)` sends `(0, w)` to `(0, ζ^g w)`. -/
theorem tangentChartMap_tangentMap_smul (g : G5) (w : Fin 2 → ℝ) :
    tangentChartMap (isChart_rnChart 0)
        (MPolyfold.tangentMap (isScSmoothMap_smul g) (zeroTangent w)) =
      ((0 : Fin 2 → ℝ), rot (χ g) w) := by
  rw [tangentChartMap_tangentMap_of_linear (isScSmoothMap_smul g) (isChart_rnChart 0)
    (isChart_rnChart 0) (ScOperator.ofConst (rot (χ g)))
    (fun _ _ => mem_univ _) (fun x _ => ?_) (mem_univ _), tangentChartMap_zeroTangent]
  · refine Prod.ext ?_ rfl
    change rot (χ g) (0 : Fin 2 → ℝ) = 0
    exact map_zero _
  · change g • x - 0 = rot (χ g) (x - 0)
    rw [sub_zero, sub_zero]
    rfl

/-- **(ZHOU) for `ℤ/5 ⋉ ℂ`** (2021 Definition 7.4.5, p. 331): the isotropy `ζ^g ≠ 1` of `0`
moves a tangent vector of `T_0ℂ`. -/
theorem isZhou_X5 : X5.IsZhou := by
  intro y g hg
  rw [trivialSubgroup_X5, Subgroup.mem_bot]
  by_contra hne
  have hx : (rnPolyfold 2).smoothVal y = 0 := eq_zero_of_isotropy g hne
  have h2 : g.val.2 = (rnPolyfold 2).smoothVal y := g.src_val
  have h1 : g.val.1 ≠ 1 := fun h => hne (GroupoidStr.Isotropy.ext (Prod.ext h h2))
  -- a non-zero vector
  let w : Fin 2 → ℝ := cE.symm 1
  have hw : w ≠ 0 := fun h => by
    have : (1 : ℂ) = 0 := by
      rw [← cE.apply_symm_apply (1 : ℂ)]
      exact cE.map_eq_zero_iff.2 h
    exact one_ne_zero this
  have hv : zeroTangent w ∈
      (rnPolyfold 2).tangentFiber ((rnPolyfold 2).smoothIncl y 1) := by
    change (rnPolyfold 2).tangentProj (zeroTangent w) = _
    refine level_ext ?_
    exact (levelVal_tangentProj_zeroTangent w).trans hx.symm
  have e1 := hg (zeroTangent w) hv
  have hval : g.val = (g.val.1, (rnPolyfold 2).levelVal 1
      ((rnPolyfold 2).tangentProj (zeroTangent w))) :=
    Prod.ext rfl (h2.trans (hx.trans (levelVal_tangentProj_zeroTangent w).symm))
  rw [hval] at e1
  replace e1 : MPolyfold.tangentMap (isScSmoothMap_smul g.val.1) (zeroTangent w) =
      zeroTangent w :=
    (tangentMor_actionEpGroupoid isScSmoothMap_smul
      (φ := (g.val.1, (rnPolyfold 2).levelVal 1 ((rnPolyfold 2).tangentProj (zeroTangent w))))
      ((X5.mem_levelSet_src_iff _ 1).1 (MPolyfold.levelVal_mem _))
      (α := zeroTangent w) rfl).symm.trans e1
  have h4 := congrArg (tangentChartMap (isChart_rnChart 0)) e1
  rw [tangentChartMap_tangentMap_smul, tangentChartMap_zeroTangent] at h4
  have h5 : rot (χ g.val.1) w = w := congrArg Prod.snd h4
  exact hw ((rot_eq_self_iff (fun h => h1 ((χ_eq_one_iff _).1 h)) w).1 h5)

/-! ### The structure -/

/-- `|ℤ/5 ⋉ ℂ| = ℂ/ℤ₅` is paracompact. -/
theorem hasParacompactOrbitSpace_X5 : X5.HasParacompactOrbitSpace :=
  hasParacompactOrbitSpace_action isScSmoothMap_smul

/-- The bundle has the local regularity property (Propositions 7.4.22 and 8.4.3). -/
theorem isLRLocal_E5 : E5.IsLRLocal :=
  EpStrongBundle.proposition_8_4_3_isLRLocal E5 isEffective_X5
    (X5.proposition_7_4_22_of_isZhou isZhou_X5)

/-- **The strong polyfold bundle structure** `((P : ℂ × ℂ → ℂ, μ), id, id)` over `ℤ/5 ⋉ ℂ`
(Definition 16.3.1), for `p = |P|`. -/
def sqStructure : StrongPolyfoldBundleStructure A5.E.projFunctor.orbitMap where
  A := A5
  isZhou := isZhou_X5
  paracompact := hasParacompactOrbitSpace_X5
  isLRLocal := isLRLocal_E5
  Γ := Homeomorph.refl _
  γ := Homeomorph.refl _
  comm := rfl

/-- **The strong polyfold bundle `|ℂ × ℂ| → ℂ/ℤ₅`** (Definition 16.3.4). -/
def sqBundle : StrongPolyfoldBundle A5.E.projFunctor.orbitMap := ⟦sqStructure⟧

/-- `|f|` is well defined on `ℂ/ℤ₅`. -/
theorem π_sqSection_eq {x y : Fin 2 → ℝ} (h : X5.π x = X5.π y) :
    A5.E.toEpGroupoid.π (sqSection x) = A5.E.toEpGroupoid.π (sqSection y) := by
  obtain ⟨k, rfl⟩ := (action_π_eq_π_iff isScSmoothMap_smul).1 h
  refine (GroupoidStr.π_eq_π_iff _).2 ⟨⟨((k, x), sqSection x), rfl⟩, rfl, ?_⟩
  exact (sqSection_smul k x).symm

/-- **The representative `(sqStructure, f)`** of the section `|z| ↦ |(z, z²)|`
(Definition 16.3.18). -/
def sqRep : SectionRep sqBundle where
  S := sqStructure
  hS := rfl
  F := sqSection
  hF := isScFredholmSectionFunctor_sqSection.1
  f := Quotient.lift (fun x : Fin 2 → ℝ => A5.E.toEpGroupoid.π (sqSection x))
    fun _ _ h => π_sqSection_eq (Quotient.sound h)
  continuous_f := Continuous.quotient_lift (A5.E.toEpGroupoid.continuous_π.comp
    (continuous_id.prodMk contDiff_sq.continuous)) _
  isSection z := Quotient.inductionOn z fun _ => rfl
  comm _ := rfl

/-- **The sc-Fredholm section `|z| ↦ |(z, z²)|`** of `sqBundle` (Definition 16.6.1). -/
def sqFredholmSection : FredholmSection sqBundle :=
  ⟨⟦sqRep⟧, sqRep, rfl, isScFredholmSectionFunctor_sqSection⟩

/-- **`ℂ/ℤ₅` has no boundary.** -/
theorem sqBundle_boundary_eq_empty : sqBundle.polyfold.boundary = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun z hz => ?_
  obtain ⟨x, rfl⟩ := sqStructure.surjective_γπ z
  have hx := (mem_boundary_iff_obj (c := sqBundle) rfl x).1 hz
  have h : (0 : ℕ) < (rnPolyfold 2).degIndex x := hx
  have h0 : (rnPolyfold 2).degIndex x = 0 := MPolyfold.degIndex_rn x
  omega

end Polyfold.Examples.OrbifoldSquare
