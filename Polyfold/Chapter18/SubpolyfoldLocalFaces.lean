import Polyfold.Chapter18.OpenSubcategory

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.3, p. 786: the remark before Definition 17.3.7 that typical examples of subpolyfolds are
local faces, or faces if the category is face-structured.  Numbers and pages are the 2021
text's.

# Local faces are subpolyfolds

## The text, paraphrased

(p. 786) Typical examples of subpolyfolds are local faces, or faces when the category is
face-structured.  The global case is Proposition 17.3.8 (p. 787, `proposition_17_3_8` in
`PolyfoldFaces.lean`).

## What is formalized

* `MPolyfold.isScDiffeoOn_openIncl_symm` (for an open `U ⊆ X` with its sub-M-polyfold
  structure, `x ↦ x` is an sc-diffeomorphism `U → U`), `MPolyfold.degIndex_subPolyfold_open`
  (it keeps the degeneracy index), `MPolyfold.isSubMPolyfold_of_subPolyfold_open` (a
  sub-M-polyfold of the open `U` is one of `X`).
* `degIndex_openSub`: the degeneracy index of the polyfold `C_V` (`openSubConstruction`) is that
  of `C`; `degIndexVia_subOrbitMap`: `|C_V| → |C|` keeps `d_{|·|}`.
* **`isSubpolyfold_of_isFaceIn`**: for a tame `C` with `F(α) ≠ ∅` for all `α`, an open
  face-structured `V ⊆ |C|` (Definition 2.7.6 (1) for `d_{|C|}`) and a face `θ` of `V` (the
  closure in `V` of a connected component of `{z ∈ V | d_{|C|}(z) = 1}`), the full subcategory
  `π⁻¹(θ)` is a subpolyfold of `C` (Definition 17.3.1).  For `V = |C|` this is Proposition 17.3.8.
* Witness: `quadrant_isSubpolyfold_of_isFaceIn` (the quadrant polyfold `[0,∞)² ⊕ W`, a face
  through the corner, `V = |C|`).

## Readings

* "Local face" is read as in Part I (Theorem 2.5.17, Definition 2.7.6): a face of an open
  face-structured subset `V` of `|C|`, for the degeneracy index `d_{|C|}` of `PolyfoldFaces.lean`.
* The proof passes to the polyfold `C_V` of Chapter 18 (`openSubConstruction`), where `θ`
  becomes a face of a face-structured polyfold, applies Proposition 17.3.8 there, and returns
  to `C` through the open inclusions `Ψ⁻¹(π⁻¹ V) ⊆ O`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

universe u

namespace Polyfold

/-! ### Open subsets as sub-M-polyfolds -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

open scoped Classical in
/-- For an open `U ⊆ X` with its sub-M-polyfold structure, `x ↦ x` is an sc-diffeomorphism
`U → U` (inverse of the inclusion). -/
theorem isScDiffeoOn_openIncl_symm {U : Set X} (hU : P.IsSubMPolyfold U) (hUo : IsOpen U)
    [ParacompactSpace U] (a : U) :
    P.IsScDiffeoOn (subPolyfold hU) (fun x => if h : x ∈ U then ⟨x, h⟩ else a) Subtype.val
      U univ where
  isScSmoothOn := isScSmoothOn_subPolyfold_of_val hU
    ((isScSmoothMap_id.mono hUo (subset_univ _)).congr fun x hx => by
      simp only [dif_pos (show x ∈ U from hx)]; rfl)
  isScSmoothOn_inv := subPolyfold_inclusion_isScSmooth hU
  mapsTo _ _ := mem_univ _
  mapsTo_inv b _ := b.2
  left_inv x hx := by simp only [dif_pos (show x ∈ U from hx)]
  right_inv b _ := by simp

/-- The sub-M-polyfold structure of an open `U ⊆ X` keeps the degeneracy index. -/
theorem degIndex_subPolyfold_open {U : Set X} (hU : P.IsSubMPolyfold U) (hUo : IsOpen U)
    [ParacompactSpace U] (q : U) : (subPolyfold hU).degIndex q = P.degIndex q.1 := by
  have h := proposition_2_4_4 (isScDiffeoOn_openIncl_symm hU hUo q) q.2
  rw [h]
  congr 1
  simp

/-- **A sub-M-polyfold of an open `U ⊆ X` is a sub-M-polyfold of `X`.** -/
theorem isSubMPolyfold_of_subPolyfold_open {U : Set X} (hU : P.IsSubMPolyfold U)
    (hUo : IsOpen U) [ParacompactSpace U] {B : Set X} (hBU : B ⊆ U)
    (hB : (subPolyfold hU).IsSubMPolyfold (Subtype.val ⁻¹' B)) : P.IsSubMPolyfold B := by
  classical
  refine isSubMPolyfold_of_forall_isScDiffeoOn fun x hx => ⟨U, univ, _, Subtype.val, _, hBU hx,
    isScDiffeoOn_openIncl_symm hU hUo ⟨x, hBU hx⟩, hB, ?_⟩
  ext y
  constructor
  · rintro ⟨hyB, hyU⟩
    refine ⟨hyU, ?_⟩
    simp only [mem_preimage, dif_pos hyU]
    exact hyB
  · rintro ⟨hyU, hy⟩
    simp only [mem_preimage, dif_pos hyU] at hy
    exact ⟨hy, hyU⟩

end MPolyfold

/-! ### Local faces -/

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} {S : C.PolyfoldConstruction}

/-- **The degeneracy index of `C_V` is that of `C`** (Definition 17.1.30 for `(F_V, M)`). -/
theorem degIndex_openSub (hu : S.HasUniformizers) {V : Set C.toGroupoidStr.OrbitSpace}
    (hVo : IsOpen V) (α : (C.openSub V).Obj) :
    (S.openSubConstruction hVo).degIndex α = S.degIndex (show C.objOver V from α).1 := by
  obtain ⟨Ψ, hΨ⟩ := hu (show C.objOver V from α).1
  obtain ⟨q, hq⟩ := S.isAt _ Ψ hΨ
  have hq' : Ψ.obj q = (show C.objOver V from α).1 := hq
  have hqV : q ∈ Ψ.obj ⁻¹' C.objOver V := by
    change Ψ.obj q ∈ C.objOver V
    rw [hq']; exact (show C.objOver V from α).2
  have hL : Ψ.restrictOver hVo ∈ (S.openSubConstruction hVo).F α :=
    (mem_openSubConstruction_F_iff hVo α _).2 ⟨Ψ, hΨ, rfl⟩
  have h1 := (S.openSubConstruction hVo).degIndex_eq ⟨Ψ.restrictOver hVo, α, hL⟩
    (q := (⟨q, hqV⟩ : Ψ.obj ⁻¹' C.objOver V)) (by
      change (C.toGroupoidStr.fullSub (C.objOver V)).Isomorphic ⟨Ψ.obj q, hqV⟩ α
      rw [show (⟨Ψ.obj q, hqV⟩ : C.objOver V) = α from Subtype.ext hq']
      exact GroupoidStr.isomorphic_refl _ _)
  have h2 := S.degIndex_eq ⟨Ψ, _, hΨ⟩ (q := q) (by
    change C.toGroupoidStr.Isomorphic (Ψ.obj q) _
    rw [hq']; exact GroupoidStr.isomorphic_refl _ _)
  rw [h1, h2]
  exact MPolyfold.degIndex_subPolyfold_open (Ψ.isSubMPolyfold_preimage_objOver hVo)
    (Ψ.isOpen_preimage_objOver hVo) ⟨q, hqV⟩

/-- **`|C_V| → |C|` keeps `d_{|·|}`.** -/
theorem degIndexVia_subOrbitMap (hu : S.HasUniformizers) (c : S.CoveringFamily)
    {V : Set C.toGroupoidStr.OrbitSpace} (hVo : IsOpen V)
    (cV : (S.openSubConstruction hVo).CoveringFamily)
    (w : (C.openSub V).toGroupoidStr.OrbitSpace) :
    S.degIndexVia c (C.subOrbitMap (C.objOver V) w) =
      (S.openSubConstruction hVo).degIndexVia cV w := by
  induction w using Quotient.inductionOn with | h α => ?_
  change S.degIndexVia c (C.toGroupoidStr.π α.1) =
    (S.openSubConstruction hVo).degIndexVia cV ((C.openSub V).toGroupoidStr.π α)
  rw [S.degIndexVia_π c, (S.openSubConstruction hVo).degIndexVia_π cV, degIndex_openSub hu hVo]

/-- **Local faces are subpolyfolds** (p. 786): for a tame `C` with `F(α) ≠ ∅` for all `α`, an
open face-structured `V ⊆ |C|` and a face `θ` of `V` (for the degeneracy index `d_{|C|}`), the
full subcategory `π⁻¹(θ)` is a subpolyfold of `C` (Definition 17.3.1).  For `V = |C|` this is
Proposition 17.3.8. -/
theorem isSubpolyfold_of_isFaceIn (hu : S.HasUniformizers) (hT : S.IsTame)
    (c : S.CoveringFamily) {V θ : Set C.toGroupoidStr.OrbitSpace}
    (hV : TameBoundary.IsFaceStructuredOpen (S.degIndexVia c) V)
    (hθ : TameBoundary.IsFaceIn (S.degIndexVia c) V θ) :
    S.IsSubpolyfold (C.toGroupoidStr.π ⁻¹' θ) := by
  have hVo := hV.1
  have huV := hasUniformizers_openSubConstruction hVo hu
  obtain ⟨cV⟩ := (S.openSubConstruction hVo).exists_coveringFamily_iff.2
    ((S.openSubConstruction hVo).hasCoveringUniformizers_of_hasUniformizers huV)
  let _ := (C.openSub V).top
  set e := C.subOrbitMap (C.objOver V) with he_def
  have hemb := isOpenEmbedding_subOrbitMap_objOver hVo
  have hd := degIndexVia_subOrbitMap hu c hVo cV
  have hD : TameBoundary.IsDHomeoOn ((S.openSubConstruction hVo).degIndexVia cV)
      (S.degIndexVia c) e univ :=
    ⟨isOpen_univ, hemb.continuous.continuousOn, hemb.injective.injOn,
      fun U hU _ => hemb.isOpenMap U hU, fun w _ => hd w⟩
  have himg : e '' univ = V := by rw [image_univ, he_def, range_subOrbitMap_objOver]
  obtain ⟨θV, hθV, hθVe⟩ := hD.exists_isFaceIn_of_image subset_rfl (himg.symm ▸ hθ)
  have hFV : (S.openSubConstruction hVo).IsFaceStructuredVia cV := by
    refine ((S.openSubConstruction hVo).isFaceStructuredVia_iff_isFaceStructuredOpen cV).2
      ⟨isTame_openSubConstruction hVo hT, isOpen_univ, fun y _ => ?_⟩
    have h1 := hD.encard_facesThrough_image subset_rfl (mem_univ y)
    have hy : e y ∈ V := himg ▸ mem_image_of_mem e (mem_univ y)
    have h2 := (congrArg (fun s => (TameBoundary.facesThrough (S.degIndexVia c) s (e y)).encard)
      himg).trans (hV.2 (e y) hy)
    exact h1.symm.trans (h2.trans (congrArg (fun n : ℕ => (n : ℕ∞)) (hd y)))
  have hsub := ((S.openSubConstruction hVo).proposition_17_3_8 cV hFV
    (((S.openSubConstruction hVo).isFaceVia_iff_isFaceIn cV θV).2 hθV)).2
  have hθsub : θ ⊆ V := by
    obtain ⟨p, _, _, rfl⟩ := hθ
    exact inter_subset_left
  have hmem : ∀ β : C.objOver V,
      (C.openSub V).toGroupoidStr.π β ∈ θV ↔ C.toGroupoidStr.π β.1 ∈ θ := by
    intro β
    constructor
    · intro h
      rw [← hθVe]
      exact ⟨_, h, rfl⟩
    · intro h
      rw [← hθVe] at h
      obtain ⟨w, hw, hwe⟩ := h
      have : w = (C.openSub V).toGroupoidStr.π β := hemb.injective hwe
      rwa [← this]
  refine ⟨isSaturated_π_preimage θ, fun α hα Ψ hΨ => ?_⟩
  have hαV : α ∈ C.objOver V := hθsub hα
  have hL : Ψ.restrictOver hVo ∈ (S.openSubConstruction hVo).F ⟨α, hαV⟩ :=
    (mem_openSubConstruction_F_iff hVo _ _).2 ⟨Ψ, hΨ, rfl⟩
  have h1 := hsub.2 ⟨α, hαV⟩ ((hmem ⟨α, hαV⟩).2 hα) (Ψ.restrictOver hVo) hL
  refine MPolyfold.isSubMPolyfold_of_subPolyfold_open (Ψ.isSubMPolyfold_preimage_objOver hVo)
    (Ψ.isOpen_preimage_objOver hVo) (fun q hq => hθsub hq) ?_
  have hset : (Subtype.val ⁻¹' (Ψ.obj ⁻¹' (C.toGroupoidStr.π ⁻¹' θ)) :
      Set (Ψ.obj ⁻¹' C.objOver V)) =
      (Ψ.restrictOver hVo).obj ⁻¹' ((C.openSub V).toGroupoidStr.π ⁻¹' θV) := by
    ext q
    exact (hmem ⟨Ψ.obj q.1, q.2⟩).symm
  rw [hset]
  exact h1

/-! ### Witness -/

section QuadrantWitness

open MPolyfold TameBoundaryExample

variable (W : ScBanach)

/-- **Witness**: in the quadrant polyfold `[0,∞)² ⊕ W` (tame, `F(α) ≠ ∅`), `V = |C|` is
face-structured, a face `θ` of `V` passes through the corner, and `π⁻¹(θ)` is a subpolyfold by
`isSubpolyfold_of_isFaceIn`. -/
theorem quadrant_isSubpolyfold_of_isFaceIn :
    ∃ θ, TameBoundary.IsFaceStructuredOpen
        ((quadrantConstruction W).degIndexVia (quadrantFamily W)) univ ∧
      TameBoundary.IsFaceIn ((quadrantConstruction W).degIndexVia (quadrantFamily W)) univ θ ∧
      (GroupoidStr.translation Unit (quadrant 2 W 0)).π (quadrantCorner W) ∈ θ ∧
      (quadrantConstruction W).IsSubpolyfold
        ((GroupoidStr.translation Unit (quadrant 2 W 0)).π ⁻¹' θ) := by
  obtain ⟨hT, hF, -, -, θ, hθ, hz, -⟩ := quadrant_proposition_17_3_8 W
  have hV := (((quadrantConstruction W).isFaceStructuredVia_iff_isFaceStructuredOpen _).1 hF).2
  have hθ' := ((quadrantConstruction W).isFaceVia_iff_isFaceIn _ θ).1 hθ
  exact ⟨θ, hV, hθ', hz, isSubpolyfold_of_isFaceIn (twistConstruction_hasUniformizers _ _) hT
    (quadrantFamily W) hV hθ'⟩

end QuadrantWitness

end GCT.PolyfoldConstruction

end Polyfold
