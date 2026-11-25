import Polyfold.Examples.Path.PartI_ScOne
import Polyfold.Chapter2.TangentMap
import Polyfold.Chapter2.Metrizable
import Polyfold.Chapter2.TameBoundary
import Polyfold.Chapter7.LocalDiffeo
import Polyfold.Examples.OrbifoldSquareInfBundle

/-!
# M-polyfolds: examples (rows V2.13, V2.17, V2.22, V2.24, V2.52, V2.53)

* `Rp`: the M-polyfold `ℝ` (constant sc-structure, one chart). `isScSmoothMap_liftR_iff`: a map
  `ℝ → ℝ` is sc-smooth between M-polyfolds iff it is `C^∞`; `isScSmoothMap_liftR_sq`,
  `not_isScSmoothMap_liftR_abs`.
* `not_isScSmoothMap_const_harm`: on the M-polyfold `H` (weighted `ℓ²`), the constant map to a
  point not on level `1` is continuous and not sc-smooth.
* `metrizable_PH`: `H`, `H_1` and `H_∞` are metrizable, and `H_∞ ≠ H`.
* `tangentMap_liftR_comp`: the chain rule `T(f ∘ f) = Tf ∘ Tf` for `f(x) = x²` on `ℝ`.
* `HQ = [0,∞) ⊕ H`; `degIndex_HQ_prod`: `d_{HQ × HQ}(0, 0) = 2`.
* `degIndex_diag`: the diagonal `HQ ₓ×ₓ HQ` (fibred product of `id`, `id`) is a sub-M-polyfold
  of `HQ × HQ` with `d(0, 0) = 1`, half of `d_{HQ × HQ}(0, 0) = 2`.
-/

open Set Function Topology TopologicalSpace

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.Path

open MPolyfold

/-! ### The M-polyfold `ℝ` -/

/-- The points of the M-polyfold `ℝ`. -/
abbrev RU : Type := ↥(univ : Set (Rc 0))

/-- The M-polyfold `ℝ`: the constant sc-structure, with one chart. -/
abbrev Rp : MPolyfold RU := relOpen_univ_Rc.toMPolyfold ⟨0, mem_univ _⟩

/-- The one chart of `Rp`. -/
abbrev RpChart : MChart RU :=
  (LocalModel.ofRelOpen relOpen_univ_Rc).selfChart ⟨0, mem_univ _⟩

theorem isChart_RpChart : Rp.IsChart RpChart := relOpen_univ_Rc.selfChart_isChart _

/-- A map `g : ℝ → ℝ`, as a map of `Rp`. -/
def liftR (g : ℝ → ℝ) : RU → RU := fun x => ⟨g (x : ℝ), mem_univ _⟩

theorem rep_liftR (g : ℝ → ℝ) : (RpChart ∘ liftR g ∘ RpChart.symm) = g := by
  funext z
  change g ((RpChart.symm z : RU) : ℝ) = g z
  congr 1
  exact RpChart.apply_symm_apply (mem_univ z)

theorem image_RpChart : RpChart '' univ = (univ : Set (Rc 0)) := by
  ext z
  exact ⟨fun _ => mem_univ z, fun _ => ⟨⟨z, mem_univ z⟩, mem_univ _, rfl⟩⟩

theorem retract_id_Rc : (ScRetraction.id relOpen_univ_Rc).retract = RpChart '' univ := by
  rw [image_RpChart]
  exact image_id _

/-- Row V2.13, Definition 2.3.8 (p. 37): a map of the M-polyfold `ℝ` (constant sc-structure,
one chart) is sc-smooth iff it is `C^∞`. -/
theorem isScSmoothMap_liftR_iff (g : ℝ → ℝ) : Rp.IsScSmoothMap Rp (liftR g) ↔ ContDiff ℝ ∞ g := by
  constructor
  · intro h
    have h1 := h.smooth RpChart RpChart isChart_RpChart isChart_RpChart univ isOpen_univ
      (fun x _ => ⟨mem_univ x, mem_univ x⟩) (fun _ _ => mem_univ _)
    rw [rep_liftR] at h1
    have h2 := h1.comp_isScSmooth (ScRetraction.id relOpen_univ_Rc) retract_id_Rc
    have h3 := (isScSmooth_iff_contDiffOn_const relOpen_univ_Rc.isScDomain g).1 h2
    exact contDiffOn_univ.1 h3
  · intro hg
    refine IsScSmoothOn.of_exists_charts isOpen_univ
      ((hg.continuous.comp continuous_subtype_val).subtype_mk fun _ => mem_univ _).continuousOn
      fun x _ =>
      ⟨RpChart, RpChart, univ, isChart_RpChart, isChart_RpChart, isOpen_univ, mem_univ x,
        fun y _ => ⟨mem_univ y, mem_univ y⟩, fun _ _ => mem_univ _, ?_⟩
    rw [rep_liftR, image_RpChart]
    refine (isScSmoothRetractMap_iff_exists relOpen_univ_Rc.isScRetract).2
      ⟨fun _ _ => mem_univ _, ScRetraction.id relOpen_univ_Rc, image_id _, ?_⟩
    exact (isScSmooth_iff_contDiffOn_const relOpen_univ_Rc.isScDomain g).2 hg.contDiffOn

/-- Row V2.13, an example: `x ↦ x²` is an sc-smooth map of the M-polyfold `ℝ`. -/
theorem isScSmoothMap_liftR_sq : Rp.IsScSmoothMap Rp (liftR fun x => x ^ 2) :=
  (isScSmoothMap_liftR_iff _).2 (contDiff_id.pow 2)

/-- Row V2.13, a non-example: `x ↦ |x|` is a continuous map of the M-polyfold `ℝ` which is not
sc-smooth. -/
theorem not_isScSmoothMap_liftR_abs :
    Continuous (liftR fun x => |x|) ∧ ¬ Rp.IsScSmoothMap Rp (liftR fun x => |x|) := by
  refine ⟨(continuous_abs.comp continuous_subtype_val).subtype_mk _, fun h => ?_⟩
  rw [isScSmoothMap_liftR_iff] at h
  exact not_differentiableAt_abs_zero (h.differentiable (by simp) 0)

/-! ### The M-polyfold `H` -/

section H

open OrbifoldSquareInf WeightedEllTwo

/-- `(1/(k+1))_k ∈ H_0` is not on level `1` of the M-polyfold `H`. -/
theorem hpt_harmH_not_mem_levelSet_one : hpt harmH ∉ PH.levelSet 1 := fun h =>
  let ⟨y, hy⟩ := (LocalBundle.mem_levelSet_iff relOpen_H h0).1 h
  incl_ne_harm y hy

theorem h0_mem_levelSet_one : h0 ∈ PH.levelSet 1 :=
  (LocalBundle.mem_levelSet_iff relOpen_H h0).2 ⟨0, map_zero _⟩

/-- Row V2.13, a non-example in infinite dimensions: on the M-polyfold `H` (the weighted `ℓ²`
scale, one chart) the constant map with value `(1/(k+1))_k` is continuous but not sc-smooth,
since sc-smooth maps preserve the levels. -/
theorem not_isScSmoothMap_const_harm :
    Continuous (fun _ : HObj => hpt harmH) ∧ ¬ PH.IsScSmoothMap PH (fun _ : HObj => hpt harmH) :=
  ⟨continuous_const, fun h => hpt_harmH_not_mem_levelSet_one
    (IsScSmoothMap.mapsTo_levelSet h 1 h0_mem_levelSet_one)⟩

/-- Row V2.17, Theorem 2.3.10 (p. 37), for the M-polyfold `H`: `H`, `H_1` and `H_∞` (with the
initial topology of the inclusions) are metrizable, and `H_∞` is a proper subset of `H`. -/
theorem metrizable_PH :
    MetrizableSpace HObj ∧ MetrizableSpace (PH.Level 1) ∧ MetrizableSpace PH.SmoothLevel ∧
      hpt harmH ∉ PH.smoothSet :=
  ⟨PH.metrizableSpace, PH.metrizableSpace_level 1, PH.metrizableSpace_smoothLevel,
    fun h => harmH_not_mem_smooth ((LocalBundle.mem_smoothSet_iff relOpen_H h0).1 h)⟩

/-- Row V2.24, a non-example: the single point `(1/(k+1))_k`, which is not a smooth point, is not
a sub-M-polyfold of `H`: a retraction onto it would be constant, and sc-smooth maps preserve
level `1`. -/
theorem not_isSubMPolyfold_harm : ¬ PH.IsSubMPolyfold {hpt harmH} := by
  intro hA
  set D := hA.data (mem_singleton (hpt harmH))
  have hV : hpt harmH ∈ D.V := hA.mem_data_V _
  have hVo : IsOpen ((Subtype.val : HObj → H 0) '' D.V) :=
    isOpen_univ.isOpenMap_subtype_val _ D.isOpen
  obtain ⟨_, ⟨v, hv, rfl⟩, hs⟩ := (H.dense_smooth 0).inter_open_nonempty _ hVo ⟨_, _, hV, rfl⟩
  obtain ⟨y, hy⟩ := H.mem_smooth_iff.1 hs 1
  have hv1 : v ∈ PH.levelSet 1 := (LocalBundle.mem_levelSet_iff relOpen_H h0).2 ⟨y, hy⟩
  have hr := IsScSmoothOn.mapsTo_levelSet D.isScSmoothOn 1 ⟨hv, hv1⟩
  have hrv : D.r v ∈ ({hpt harmH} : Set HObj) ∩ D.V := D.image ▸ mem_image_of_mem D.r hv
  rw [mem_singleton_iff.1 hrv.1] at hr
  exact hpt_harmH_not_mem_levelSet_one hr

end H

/-! ### The tangent map -/

/-- Row V2.22, the chain rule on an example: for `f(x) = x²` on the M-polyfold `ℝ`,
`T(f ∘ f) = Tf ∘ Tf`, and `Tf` covers `f`. -/
theorem tangentMap_liftR_comp :
    MPolyfold.tangentMap (isScSmoothMap_liftR_sq.comp isScSmoothMap_liftR_sq) =
        MPolyfold.tangentMap isScSmoothMap_liftR_sq ∘ MPolyfold.tangentMap isScSmoothMap_liftR_sq ∧
      ∀ α, Rp.levelVal 1 (Rp.tangentProj (MPolyfold.tangentMap isScSmoothMap_liftR_sq α)) =
        liftR (fun x => x ^ 2) (Rp.levelVal 1 (Rp.tangentProj α)) :=
  ⟨tangentMap_comp _ _, levelVal_tangentProj_tangentMap _⟩

/-! ### Products and fibred products: `[0,∞) ⊕ H` -/

section Quadrant

open WeightedEllTwo

/-- The points of the quadrant `[0,∞) ⊕ H`. -/
abbrev HQo : Type := ↥(quadrant 1 H 0)

/-- The M-polyfold `[0,∞) ⊕ H` (one chart), `H` the weighted `ℓ²` scale. -/
abbrev HQ : MPolyfold HQo := quadrantPolyfold 1 H

/-- The corner `(0, 0)` of `[0,∞) ⊕ H`. -/
def o : HQo := ⟨0, zero_mem_quadrant 1 H⟩

instance : ParacompactSpace (HQo × HQo) := paracompactSpace_prod HQ HQ

/-- Row V2.52, products of M-polyfolds: `d_{X × X}(0, 0) = d_X(0) + d_X(0) = 2` for the tame
`X = [0,∞) ⊕ H`, whose corner has `d_X(0) = 1`; `X × X` is tame. -/
theorem degIndex_HQ_prod :
    HQ.degIndex o = 1 ∧ (HQ.prod HQ).IsTame ∧ (HQ.prod HQ).degIndex (o, o) = 2 := by
  have h := isTame_prod HQ HQ (quadrantPolyfold_isTame 1 H) (quadrantPolyfold_isTame 1 H)
  have h1 : HQ.degIndex o = 1 := quadrantPolyfold_degIndex_zero 1 H
  exact ⟨h1, h.1, by rw [h.2, h1]⟩

instance : ParacompactSpace (fibredProduct (id : HQo → HQo) id) :=
  paracompactSpace_of_isClosed (isClosed_fibredProduct continuous_id continuous_id)

/-- The diagonal of `X × X` is a sub-M-polyfold: the fibred product of `id` and `id`. -/
theorem isSubMPolyfold_diag :
    (HQ.prod HQ).IsSubMPolyfold (fibredProduct (id : HQo → HQo) id) :=
  isSubMPolyfold_fibredProduct (S := HQ) isLocalScDiffeo_id isLocalScDiffeo_id.isScSmoothMap

/-- The corner `((0, 0), (0, 0))` of the diagonal. -/
def oo : fibredProduct (id : HQo → HQo) id := ⟨(o, o), rfl⟩

/-- Row V2.53, Proposition 2.5.20 (p. 63), and row V2.24, Proposition 2.3.19 (p. 42): the diagonal
`X ₓ×_{id} X` of `X = [0,∞) ⊕ H` is a sub-M-polyfold of `X × X`; at the corner its degeneracy
index is `d_X(0) = 1`, half of `d_{X × X}(0, 0) = 2`. -/
theorem degIndex_diag :
    (subPolyfold isSubMPolyfold_diag).degIndex oo = 1 ∧
      2 * (subPolyfold isSubMPolyfold_diag).degIndex oo = (HQ.prod HQ).degIndex (o, o) := by
  have h := proposition_2_5_20_of_isLocalScDiffeo (P := HQ) (Q := HQ) (S := HQ)
    isLocalScDiffeo_id isLocalScDiffeo_id oo
  have h1 : (subPolyfold isSubMPolyfold_diag).degIndex oo = 1 :=
    h.1.trans (quadrantPolyfold_degIndex_zero 1 H)
  exact ⟨h1, h.2.2 (quadrantPolyfold_isTame 1 H) (quadrantPolyfold_isTame 1 H)⟩

/-- Row V2.24, Proposition 2.3.19 (1) (p. 42): the inclusion of the diagonal into `X × X` is
sc-smooth. -/
theorem isScSmoothMap_diag_inclusion :
    (subPolyfold isSubMPolyfold_diag).IsScSmoothMap (HQ.prod HQ) Subtype.val :=
  subPolyfold_inclusion_isScSmooth isSubMPolyfold_diag

end Quadrant

end Polyfold.Examples.Path
