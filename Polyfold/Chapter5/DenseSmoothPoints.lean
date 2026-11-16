import Polyfold.Chapter2.Metrizable
import Polyfold.Chapter5.DenseSmooth

/-!
# Smooth points are dense

The level sets of a partial quadrant, a retract and an M-polyfold lie in the closure of the smooth
points. The groupoid form is in `Chapter7/SmoothPointsDense.lean`.
-/

open Set Filter Topology Function
noncomputable section
namespace Polyfold
universe u
variable {E : ScBanach}

/-- For a partial quadrant `C ⊆ E`, the smooth points of `C_m` are dense in `C_m`. -/
theorem IsPartialQuadrant.lvlSet_subset_closure_smooth {C : Set (E 0)}
    (hC : IsPartialQuadrant E C) (m : ℕ) :
    E.lvlSet C m ⊆ closure (E.lvlSet C m ∩ E.smoothLvl m) := by
  intro x hx
  have h1 : x ∈ closure (interior (E.lvlSet C m)) := by
    rw [(hC.convex_lvlSet m).closure_interior_eq_closure_of_nonempty_interior
      (hC.interior_lvlSet_nonempty m)]
    exact subset_closure hx
  have h2 : interior (E.lvlSet C m) ⊆ closure (interior (E.lvlSet C m) ∩ E.smoothLvl m) :=
    (E.dense_smooth m).open_subset_closure_inter isOpen_interior
  exact closure_mono (inter_subset_inter_left _ interior_subset)
    (closure_minimal h2 isClosed_closure h1)

/-- For `U` relatively open in a partial quadrant, `U_∞` is dense in every `U_m` (the fact used in
the proof of 2021 Lemma 2.2.1). -/
theorem IsRelOpenInQuadrant.lvlSet_subset_closure_smooth {C U : Set (E 0)}
    (hU : IsRelOpenInQuadrant E C U) (m : ℕ) :
    E.lvlSet U m ⊆ closure (E.lvlSet U m ∩ E.smoothLvl m) := by
  obtain ⟨O, hO, rfl⟩ := hU.relOpen
  intro x hx
  rw [ScBanach.lvlSet_inter] at hx ⊢
  have h := (E.isOpen_lvlSet hO m).inter_closure
    ⟨hx.1, hU.isPartialQuadrant.lvlSet_subset_closure_smooth m hx.2⟩
  refine closure_mono ?_ h
  rintro y ⟨hyO, hyC, hyS⟩
  exact ⟨⟨hyO, hyC⟩, hyS⟩

/-- For a retract `O = r(U)`, the smooth points of `O_m` are dense in `O_m`. -/
theorem ScRetraction.lvlSet_retract_subset_closure_smooth {C : Set (E 0)} (R : ScRetraction E C)
    (m : ℕ) : E.lvlSet R.retract m ⊆ closure (E.lvlSet R.retract m ∩ E.smoothLvl m) := by
  intro x hx
  have hxU : x ∈ E.lvlSet R.U m := R.lvlSet_retract_subset m hx
  have h0 := R.isSc1.isSc0
  have hfix : levelMap R m x = x :=
    levelMap_eq_of_toBase_eq (R.apply_eq_self_of_mem_retract hx).symm
  have hcont : ContinuousWithinAt (levelMap R m) (E.lvlSet R.U m ∩ E.smoothLvl m) x :=
    ((h0.continuousOn m) x hxU).mono inter_subset_left
  have hcl := hcont.mem_closure_image (R.relOpen.lvlSet_subset_closure_smooth m hxU)
  rw [hfix] at hcl
  refine closure_mono ?_ hcl
  rintro _ ⟨e, ⟨heU, heS⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [ScBanach.mem_lvlSet, h0.toBase_levelMap heU]
    exact ⟨_, heU, rfl⟩
  · change E.toBase m (levelMap R m e) ∈ E.smooth
    rw [h0.toBase_levelMap heU, E.mem_smooth_iff]
    intro j
    obtain ⟨y, hy⟩ := E.mem_smooth_iff.1 (show E.toBase m e ∈ E.smooth from heS) j
    have hyU : y ∈ E.lvlSet R.U j := by rw [ScBanach.mem_lvlSet, hy]; exact heU
    have := h0.mem_range j y hyU
    rwa [hy] at this

/-- For a retract `(O, C, E)`, the smooth points of `O_m` are dense in `O_m`. -/
theorem IsScRetract.lvlSet_subset_closure_smooth {C O : Set (E 0)} (h : IsScRetract E C O)
    (m : ℕ) : E.lvlSet O m ⊆ closure (E.lvlSet O m ∩ E.smoothLvl m) := by
  obtain ⟨R, rfl⟩ := h
  exact R.lvlSet_retract_subset_closure_smooth m

namespace MPolyfold
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

variable {P} in
/-- A point of a chart domain whose image is a smooth point of `E` is a smooth point of `X`. -/
theorem mem_smoothSet_of_chart {φ : MChart X} (hφ : P.IsChart φ) {x : X} (hx : x ∈ φ.source)
    (h : φ x ∈ φ.model.E.smooth) : x ∈ P.smoothSet :=
  mem_iInter.2 fun j => (P.mem_levelSet_iff hφ hx).2 (φ.model.E.mem_smooth_iff.1 h j)

/-- **2021 p. 289 (2017 p. 227), gap G.73**: for every M-polyfold `X` and every `m`, the smooth
points `X_∞` are dense in `X_m` (with the topology of `X_m`).  This is Chapter 7's hypothesis
`DenseSmooth`. -/
theorem denseSmooth : P.DenseSmooth := by
  intro m
  refine dense_iff_inter_open.2 fun S hS ⟨y, hyS⟩ => ?_
  obtain ⟨φ, hφ, hyφ⟩ := P.exists_isChart_mem_source (P.levelVal m y)
  have hemb := P.isEmbedding_levelLift hφ m
  have hSV : IsOpen ((Subtype.val : (P.levelVal m ⁻¹' φ.source : Set (P.Level m)) → P.Level m) ⁻¹'
      S) := hS.preimage continuous_subtype_val
  obtain ⟨W, hW, hWeq⟩ := hemb.isInducing.isOpen_iff.1 hSV
  set z₀ := levelLift φ m (P.levelVal m y) with hz₀
  have hz₀W : z₀ ∈ W := by
    have : (⟨y, hyφ⟩ : (P.levelVal m ⁻¹' φ.source : Set (P.Level m))) ∈
        (Subtype.val ⁻¹' S : Set (P.levelVal m ⁻¹' φ.source : Set (P.Level m))) := hyS
    rw [← hWeq] at this
    exact this
  have hz₀O : z₀ ∈ φ.model.E.lvlSet φ.model.O m := by
    rw [ScBanach.mem_lvlSet, hz₀, P.toBase_levelLift hφ hyφ (levelVal_mem y)]
    exact φ.mapsTo_model _ hyφ
  obtain ⟨z, hzW, hzO, hzS⟩ := mem_closure_iff.1
    (φ.model.isScRetract.lvlSet_subset_closure_smooth m hz₀O) W hW hz₀W
  have hzO' : φ.model.E.toBase m z ∈ φ.model.O := hzO
  set x := φ.symm (φ.model.E.toBase m z) with hx
  have hxφ : x ∈ φ.source := φ.symm_mapsTo hzO'
  have hφx : φ x = φ.model.E.toBase m z := φ.apply_symm_apply hzO'
  have hxm : x ∈ P.levelSet m := (P.mem_levelSet_iff hφ hxφ).2 ⟨z, hφx.symm⟩
  have hlift : levelLift φ m x = z := by
    apply φ.model.E.toBase_injective m
    rw [P.toBase_levelLift hφ hxφ hxm, hφx]
  refine ⟨P.levelMk m x hxm, ?_, ?_⟩
  · have : (⟨P.levelMk m x hxm, hxφ⟩ : (P.levelVal m ⁻¹' φ.source : Set (P.Level m))) ∈
        (fun x : (P.levelVal m ⁻¹' φ.source : Set (P.Level m)) =>
          levelLift φ m (P.levelVal m x)) ⁻¹' W := by
      change levelLift φ m x ∈ W
      rw [hlift]; exact hzW
    rw [hWeq] at this
    exact this
  · exact mem_smoothSet_of_chart (x := x) hφ hxφ (by rw [hφx]; exact hzS)

/-- `X_∞` is dense in `X`. -/
theorem dense_smoothSet : Dense P.smoothSet := P.denseSmooth.dense

end MPolyfold
end Polyfold
end
