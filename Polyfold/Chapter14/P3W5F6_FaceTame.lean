import Polyfold.Chapter14.P3W3B1_GoodBoundary
import Polyfold.Chapter11.GapP2_H2FaceMeet
import Polyfold.Chapter2.TameFaces
import Polyfold.Chapter2.TameBoundaryStructure

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §14.1, the remark after
**Definition 14.1.2**, p. 641 (2017: after Definition 14.1): the closures `θ̄_j` of the faces of a
good neighbourhood `V(x)` are tame M-polyfolds.

# The faces of a good neighbourhood are tame M-polyfolds

## The text, paraphrased

For a good open neighbourhood `V(x)` of `x ∈ ∂X` with the components `θ_1, …, θ_{d(x)}` of
`{y ∈ V(x) | d_X(y) = 1}` (Proposition 14.1.1 (4)), the closures `θ̄_j` (in `V(x)`) are tame
M-polyfolds.

## What is formalized

* `MPolyfold.isFace_iff_isFaceIn_univ`, `MPolyfold.isFaceStructured_iff_univ`: Part I's faces and
  face structure (Definition 2.5.10) are the faces and the face structure of the open set `univ`
  (Definition 2.7.6).
* `EpGroupoid.HasBoundaryFaces.mem_of_mem_closure`, `.isFaceIn_iff`, `.injective_closure`,
  `.facesThrough_eq`: the faces of the open set `V` (Definition 2.7.6) are exactly the
  `θ̄_i = V ∩ cl(θ_i)`, pairwise distinct.
* `EpGroupoid.HasBoundaryFaces.isFaceStructuredOpen`: `V` is a face-structured open set
  ((4)(b) of Proposition 14.1.1 is the count).
* **The remark**: `EpGroupoid.HasBoundaryFaces.isSubMPolyfold` (`θ̄_i ⊆ X` is a sub-M-polyfold,
  Part I's `isSubMPolyfold_of_isFaceIn`); `EpGroupoid.HasBoundaryFaces.isFace_restrictOpen`
  (`θ̄_i` is a face of the tame face-structured M-polyfold `V`); and
  `EpGroupoid.HasBoundaryFaces.face_isTame` (with Theorem 2.5.17: `θ̄_i`, with its structure as a
  sub-M-polyfold of `V`, is a tame M-polyfold, and `d_X = d_{θ̄_i} + 1` on it);
  `EpGroupoid.IsGoodBoundaryNbhd.faces_isSubMPolyfold` for good neighbourhoods.

The only hypothesis is the chapter's standing one, `X` tame.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u

open TameBoundary

namespace MPolyfold

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] (P : MPolyfold Z)

/-- The faces of `Z` (Definition 2.5.10) are the faces of the open set `univ` (Definition 2.7.6). -/
theorem isFace_iff_isFaceIn_univ {F : Set Z} : P.IsFace F ↔ IsFaceIn P.degIndex univ F := by
  simp only [IsFace, IsFaceIn, faceAt, univ_inter, mem_univ, true_and]

/-- `Z` is face-structured (Definition 2.5.10) iff `univ` is a face-structured open set
(Definition 2.7.6). -/
theorem isFaceStructured_iff_univ :
    P.IsFaceStructured ↔ IsFaceStructuredOpen P.degIndex univ := by
  have h : ∀ x, {F : Set Z | P.IsFace F ∧ x ∈ F} = facesThrough P.degIndex univ x := fun x => by
    ext F
    simp only [mem_ofPred_eq, facesThrough, P.isFace_iff_isFaceIn_univ]
  refine ⟨fun h' => ⟨isOpen_univ, fun x _ => ?_⟩, fun h' x => ?_⟩
  · rw [← h x]; exact h' x
  · rw [h x]; exact h'.2 x (mem_univ x)

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {x : Obj} {V : Set Obj} {θ : Fin (X.PObj.degIndex x) → Set Obj}

namespace HasBoundaryFaces

variable (h : X.HasBoundaryFaces x V θ)
include h

/-- A point of `V` with `d = 1` in `cl(θ_i)` lies in `θ_i` (a component of
`{y ∈ V | d(y) = 1}` is closed in it). -/
theorem mem_of_mem_closure (i : Fin (X.PObj.degIndex x)) {p : Obj} (hpV : p ∈ V)
    (hp1 : X.PObj.degIndex p = 1) (hp : p ∈ closure (θ i)) : p ∈ θ i := by
  obtain ⟨q, hqV, hq1, hθ⟩ := h.isComponent i
  rw [hθ] at hp ⊢
  have hs : IsPreconnected
      (insert p (connectedComponentIn (V ∩ {y | X.PObj.degIndex y = 1}) q)) :=
    isPreconnected_connectedComponentIn.subset_closure (subset_insert _ _)
      (insert_subset hp subset_closure)
  have hqF : q ∈ V ∩ {y | X.PObj.degIndex y = 1} := ⟨hqV, hq1⟩
  have hpF : p ∈ V ∩ {y | X.PObj.degIndex y = 1} := ⟨hpV, hp1⟩
  exact hs.subset_connectedComponentIn (mem_insert_of_mem _ (mem_connectedComponentIn hqF))
    (insert_subset hpF (connectedComponentIn_subset _ _)) (mem_insert p _)

/-- `θ̄_i = V ∩ cl(θ_i)` is the face of `V` through any point of `θ_i`. -/
theorem eq_faceAt (i : Fin (X.PObj.degIndex x)) {p : Obj} (hp : p ∈ θ i) :
    V ∩ closure (θ i) = faceAt X.PObj.degIndex V p := by
  obtain ⟨q, -, -, hθ⟩ := h.isComponent i
  rw [hθ] at hp ⊢
  rw [faceAt, connectedComponentIn_eq hp]

/-- `θ̄_i` is a face of the open set `V` (Definition 2.7.6). -/
theorem isFaceIn (i : Fin (X.PObj.degIndex x)) : IsFaceIn X.PObj.degIndex V (V ∩ closure (θ i)) := by
  obtain ⟨q, hqV, hq1, hθ⟩ := h.isComponent i
  exact ⟨q, hqV, hq1, by rw [hθ]; rfl⟩

/-- The faces of `V` are exactly the `θ̄_i`. -/
theorem isFaceIn_iff {γ : Set Obj} :
    IsFaceIn X.PObj.degIndex V γ ↔ ∃ i, γ = V ∩ closure (θ i) := by
  constructor
  · rintro ⟨p, hpV, hp1, rfl⟩
    have h1 : (1 : ℕ∞) ≤ {i | p ∈ V ∩ closure (θ i)}.encard := by
      rw [h.deg_eq p hpV, hp1]; simp
    obtain ⟨i, hi⟩ := Set.one_le_encard_iff_nonempty.1 h1
    exact ⟨i, (h.eq_faceAt i (h.mem_of_mem_closure i hpV hp1 hi.2)).symm⟩
  · rintro ⟨i, rfl⟩
    exact h.isFaceIn i

/-- The `θ̄_i` are pairwise distinct. -/
theorem injective_closure : Injective fun i => V ∩ closure (θ i) := by
  intro i j hij
  have hij' : V ∩ closure (θ i) = V ∩ closure (θ j) := hij
  obtain ⟨q, hqV, hq1, hθ⟩ := h.isComponent i
  have hqi : q ∈ θ i := by rw [hθ]; exact mem_connectedComponentIn (show q ∈ V ∩ {y | X.PObj.degIndex y = 1} from ⟨hqV, hq1⟩)
  have hqj : q ∈ θ j := by
    have : q ∈ V ∩ closure (θ j) := hij' ▸ ⟨hqV, subset_closure hqi⟩
    exact h.mem_of_mem_closure j hqV hq1 this.2
  apply h.injective
  obtain ⟨q', -, -, hθ'⟩ := h.isComponent j
  rw [hθ, hθ']
  rw [hθ'] at hqj
  exact (connectedComponentIn_eq hqj).symm

/-- The faces of `V` through `y` are the `θ̄_i ∋ y`. -/
theorem facesThrough_eq (y : Obj) :
    facesThrough X.PObj.degIndex V y =
      (fun i => V ∩ closure (θ i)) '' {i | y ∈ V ∩ closure (θ i)} := by
  ext γ
  constructor
  · rintro ⟨hγ, hyγ⟩
    obtain ⟨i, rfl⟩ := h.isFaceIn_iff.1 hγ
    exact ⟨i, hyγ, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨h.isFaceIn i, hi⟩

/-- **`V` is a face-structured open set** (Definition 2.7.6): (4)(b) of Proposition 14.1.1 counts
the faces of `V` through each point. -/
theorem isFaceStructuredOpen (hV : IsOpen V) : IsFaceStructuredOpen X.PObj.degIndex V :=
  ⟨hV, fun y hy => by
    rw [h.facesThrough_eq y, h.injective_closure.injOn.encard_image, h.deg_eq y hy]⟩

/-- **The remark after Definition 14.1.2, p. 641**, as sub-M-polyfolds of `X`: each
`θ̄_i ⊆ X` is a sub-M-polyfold (Part I's argument for Theorem 2.5.17 on the face-structured open
set `V`). -/
theorem isSubMPolyfold (hX : X.IsTame) (hV : IsOpen V) (i : Fin (X.PObj.degIndex x)) :
    X.PObj.IsSubMPolyfold (V ∩ closure (θ i)) :=
  X.PObj.isSubMPolyfold_of_isFaceIn hX (h.isFaceStructuredOpen hV) (h.isFaceIn i)

/-- The M-polyfold `V` (with Part I's `restrictOpen`) is face structured. -/
theorem isFaceStructured_restrictOpen (hV : IsOpen V) [Nonempty V] [ParacompactSpace V] :
    (X.PObj.restrictOpen hV).IsFaceStructured :=
  (MPolyfold.isFaceStructured_iff_univ _).2
    (MPolyfold.isFaceStructuredOpen_restrictOpen X.PObj hV (h.isFaceStructuredOpen hV))

/-- `θ̄_i` (as a subset of `V`) is a face of the M-polyfold `V` (Definition 2.5.10). -/
theorem isFace_restrictOpen (hV : IsOpen V) [Nonempty V] [ParacompactSpace V]
    (i : Fin (X.PObj.degIndex x)) :
    (X.PObj.restrictOpen hV).IsFace (Subtype.val ⁻¹' (V ∩ closure (θ i))) := by
  have h' : IsFaceIn X.PObj.degIndex (Subtype.val '' (univ : Set V)) (V ∩ closure (θ i)) := by
    rw [image_univ, Subtype.range_coe]; exact h.isFaceIn i
  obtain ⟨γ, hγ, hγe⟩ :=
    (MPolyfold.isDHomeoOn_subtypeVal X.PObj hV).exists_isFaceIn_of_image subset_rfl h'
  rw [MPolyfold.isFace_iff_isFaceIn_univ, ← hγe, Subtype.val_injective.preimage_image]
  exact hγ

/-- **The remark after Definition 14.1.2, p. 641 (2017: after Definition 14.1)**: for tame `X`,
each `θ̄_i` (a face of the tame face-structured M-polyfold `V`, with its structure as a
sub-M-polyfold of `V`, Theorem 2.5.17) is a **tame M-polyfold**, and `d_X = d_{θ̄_i} + 1` on it. -/
theorem face_isTame (hX : X.IsTame) (hV : IsOpen V) (i : Fin (X.PObj.degIndex x)) :
    letI : ParacompactSpace V := X.PObj.paracompactSpace_subtype V
    letI : Nonempty V := ⟨⟨x, (h.mem_closure i).1⟩⟩
    letI : ParacompactSpace (Subtype.val ⁻¹' (V ∩ closure (θ i)) : Set V) :=
      MPolyfold.paracompactSpace_of_isClosed
        (MPolyfold.IsFace.isClosed _ (h.isFace_restrictOpen hV i))
    (MPolyfold.subPolyfold (MPolyfold.theorem_2_5_17_isSubMPolyfold_face _
      (MPolyfold.isTame_restrictOpen X.PObj hV hX) (h.isFaceStructured_restrictOpen hV)
      (h.isFace_restrictOpen hV i))).IsTame ∧
    ∀ v : (Subtype.val ⁻¹' (V ∩ closure (θ i)) : Set V), X.PObj.degIndex (v : V) =
      (MPolyfold.subPolyfold (MPolyfold.theorem_2_5_17_isSubMPolyfold_face _
        (MPolyfold.isTame_restrictOpen X.PObj hV hX) (h.isFaceStructured_restrictOpen hV)
        (h.isFace_restrictOpen hV i))).degIndex v + 1 := by
  let _ : ParacompactSpace V := X.PObj.paracompactSpace_subtype V
  let _ : Nonempty V := ⟨⟨x, (h.mem_closure i).1⟩⟩
  obtain ⟨h1, h2⟩ := MPolyfold.theorem_2_5_17_isTame_face _
    (MPolyfold.isTame_restrictOpen X.PObj hV hX) (h.isFaceStructured_restrictOpen hV)
    (h.isFace_restrictOpen hV i)
  refine ⟨h1, fun v => ?_⟩
  rw [← MPolyfold.degIndex_restrictOpen X.PObj hV (v : V)]
  exact h2 v

end HasBoundaryFaces

/-- **The remark after Definition 14.1.2** for a good open neighbourhood `V(x)` (Definition
14.1.2) of a tame `X`: `V(x)` is a face-structured open set whose faces are the `θ̄_i`, and each
`θ̄_i` is a sub-M-polyfold of `X` (tame by `HasBoundaryFaces.face_isTame`). -/
theorem IsGoodBoundaryNbhd.faces_isSubMPolyfold (hX : X.IsTame) {V : X.NatNbhd x}
    (hV : X.IsGoodBoundaryNbhd V) :
    ∃ θ, X.HasBoundaryFaces x V.U θ ∧ IsFaceStructuredOpen X.PObj.degIndex V.U ∧
      ∀ i, X.PObj.IsSubMPolyfold (V.U ∩ closure (θ i)) := by
  obtain ⟨θ, hθ⟩ := hV.hasFaces
  exact ⟨θ, hθ, hθ.isFaceStructuredOpen V.isOpen_U, fun i => hθ.isSubMPolyfold hX V.isOpen_U i⟩

end EpGroupoid

end Polyfold
