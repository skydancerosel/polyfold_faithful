import Polyfold.Chapter5.RestrictOpen

/-!
# Smoothness of the subtype inclusion

The inclusion of an open subset is sc-smooth. The local tangent constructions are in
`Chapter8/TangentLocal.lean`.
-/

open Set Filter Topology Function
noncomputable section
namespace Polyfold
namespace MPolyfold
universe u v w
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {S : MPolyfold Z}
section OpenSubset
variable {U : Set X} (hU : IsOpen U) [Nonempty U] [ParacompactSpace U]

include hU in
/-- The inclusion `U → X` of an open subset (with Part I's structure `restrictOpen`) is sc-smooth:
in the charts `φ|U` of `U` and `φ|U` of `X` it is the identity. -/
theorem isScSmoothMap_subtypeVal : (P.restrictOpen hU).IsScSmoothMap P (Subtype.val : U → X) := by
  refine IsScSmoothOn.of_exists_charts isOpen_univ continuous_subtype_val.continuousOn
    fun v _ => ?_
  obtain ⟨φ, hφ, hv⟩ := P.exists_isChart_mem_source v.1
  set φ' := φ.restrict (s := φ.source ∩ U) inter_subset_left (φ.isOpen_source.inter hU) with hφ'
  have hφ'c : P.IsChart φ' := MPolyfold.IsChart.restrict P hφ _ _
  set φ'' := φ'.restrictTo (V := U) inter_subset_right with hφ''
  have hφ''c : (P.restrictOpen hU).IsChart φ'' := isChart_restrictTo hU hφ'c inter_subset_right
  refine ⟨φ'', φ', φ''.source, hφ''c, hφ'c, φ''.isOpen_source, ⟨hv, v.2⟩,
    fun w hw => ⟨mem_univ _, hw⟩, fun w hw => hw, ?_⟩
  refine ((isScSmoothRetractMap_id _).mono_target
    fun z hz => φ''.image_subset_model subset_rfl hz).congr ?_
  rintro _ ⟨w, hw, rfl⟩
  simp only [Function.comp_apply, id, φ''.symm_apply_apply hw]
  rfl

end OpenSubset
end MPolyfold
end Polyfold
end
