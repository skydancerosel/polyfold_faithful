import Polyfold.Chapter11.GapP2_HFaces

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.1: **Proposition 11.1.6** (2021 p. 524; 2017: Proposition 11.2, p. 378),
the clause on the intersection of two faces.

# Two faces need not meet in a face

## The text, paraphrased

(Proposition 11.1.6) For a face structured tame ep-groupoid `X`: if the intersection of two
faces `F` and `G` is nonempty, it is a face in `F` as well as in `G`.

## What is formalized

* `MPolyfold.degIndex_restrictOpen`, `MPolyfold.isTame_restrictOpen`,
  `MPolyfold.isFaceStructuredOpen_restrictOpen`: an open subset `V` of a tame M-polyfold, with
  Part I's structure `restrictOpen`, has the same degeneracy index, is tame, and is face
  structured when `V` is a face structured open set (2021 Definition 2.7.6).
* `EpGroupoid.isEpFaceStructured_trivial_restrictOpen`: the trivial ep-groupoid of such a `V` is
  (ep-)face structured.
* `EpGroupoid.FacesMeetInFaces`: the clause as printed, for two distinct faces `X_θ ≠ X_θ'`
  of `X` (Definition 11.1.3), read in the ep-groupoid `X_θ` of Proposition 11.1.6
  (`faceEpGroupoid`): `X_θ ∩ X_θ'` is a face of `X_θ`, and `X_θ ∩ X_θ'` is a face of `X_θ'`.
* `FaceMeetExample.not_facesMeetInFaces`: **the clause does not hold as we read it.**  For
  `V = ([0,∞)³ ⊕ W) ∖ K`, `K = {p₀ + p₁ ≤ 1/4, 1 ≤ p₂ ≤ 2}` (a closed block cutting the edge
  `p₀ = p₁ = 0` at heights `[1, 2]`), the trivial ep-groupoid of `V` is face structured; the
  faces `X_θ = V ∩ {p₀ = 0}` and `X_θ' = V ∩ {p₁ = 0}` meet in the two pieces `p₂ ∈ [0, 1)`
  and `p₂ ∈ (2, ∞)` of the edge, which is a union of two faces of `X_θ` and not a face of `X_θ`
  (a face is the closure of one connected component, and `p₂ ↦ p₂` separates the two pieces).
  With `W = 0` this is a 3-manifold with boundary and corners.

The corrected form (the intersection is a union of faces of each) is in
`GapP2_H2FaceMeetUnion.lean`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

open TameBoundary

universe u

/-! ### Open subsets of tame M-polyfolds -/

namespace MPolyfold

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] (P : MPolyfold Z)
  {V : Set Z} (hV : IsOpen V) [Nonempty V] [ParacompactSpace V]

/-- The degeneracy index of an open subset is that of the ambient M-polyfold (Proposition 2.4.4
for the inclusion, an sc-diffeomorphism onto `V`). -/
theorem degIndex_restrictOpen (v : V) : (P.restrictOpen hV).degIndex v = P.degIndex v :=
  proposition_2_4_4 (isScDiffeoOn_subtypeVal hV) (mem_univ v)

/-- An open subset of a tame M-polyfold is tame. -/
theorem isTame_restrictOpen (hP : P.IsTame) : (P.restrictOpen hV).IsTame :=
  isTame_of_forall_exists_chart _ fun x =>
    (isScDiffeoOn_subtypeVal hV).exists_tame_chart hP (mem_univ x)

/-- The inclusion `V → Z` is an index-preserving homeomorphism onto the open set `V`. -/
theorem isDHomeoOn_subtypeVal :
    IsDHomeoOn (P.restrictOpen hV).degIndex P.degIndex Subtype.val univ :=
  ⟨isOpen_univ, continuous_subtype_val.continuousOn, Subtype.val_injective.injOn,
    fun U hU _ => hV.isOpenMap_subtype_val U hU, fun v _ => (degIndex_restrictOpen P hV v).symm⟩

/-- If `V` is a face structured open set of `Z` (2021 Definition 2.7.6), the M-polyfold `V` is
face structured on `univ`. -/
theorem isFaceStructuredOpen_restrictOpen (h : IsFaceStructuredOpen P.degIndex V) :
    IsFaceStructuredOpen (P.restrictOpen hV).degIndex univ := by
  refine ⟨isOpen_univ, fun y _ => ?_⟩
  have h' := (isDHomeoOn_subtypeVal P hV).encard_facesThrough_image subset_rfl (mem_univ y)
  rw [image_univ, Subtype.range_coe, h.2 _ y.2, ← degIndex_restrictOpen P hV y] at h'
  exact h'.symm

end MPolyfold

namespace EpGroupoid

/-- The trivial ep-groupoid of a face structured open subset of a tame M-polyfold is face
structured (Definition 11.1.3). -/
theorem isEpFaceStructured_trivial_restrictOpen {Z : Type u} [TopologicalSpace Z] [T2Space Z]
    [ParacompactSpace Z] (P : MPolyfold Z) {V : Set Z} (hV : IsOpen V) [Nonempty V]
    [ParacompactSpace V] (hP : P.IsTame) (h : IsFaceStructuredOpen P.degIndex V) :
    (trivial (P.restrictOpen hV)).IsEpFaceStructured :=
  isEpFaceStructured_iff.2 ⟨MPolyfold.isTame_restrictOpen P hV hP,
    (isFaceStructuredOpen_univ_iff (Examples.isHomeomorph_π_trivial _) fun _ => rfl).1
      (MPolyfold.isFaceStructuredOpen_restrictOpen P hV h)⟩

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- **The intersection clause of 2021 Proposition 11.1.6, p. 524 (2017: Proposition 11.2,
p. 378)**, as printed: for two distinct faces `X_θ`, `X_θ'` of the face structured ep-groupoid
`X` which meet, `X_θ ∩ X_θ'` is a face of the ep-groupoid `X_θ` (`faceEpGroupoid`, in the sense
of Definition 11.1.3) and a face of `X_θ'`. -/
def FacesMeetInFaces (X : EpGroupoid Obj Mor) (hX : X.IsEpFaceStructured) : Prop :=
  ∀ (θ θ' : Set X.OrbitSpace) (hθ : X.IsOrbitFace θ) (hθ' : X.IsOrbitFace θ'), θ ≠ θ' →
    (X.faceObj θ ∩ X.faceObj θ').Nonempty →
      (faceEpGroupoid hX hθ).IsEpFace (Subtype.val ⁻¹' X.faceObj θ') ∧
        (faceEpGroupoid hX hθ').IsEpFace (Subtype.val ⁻¹' X.faceObj θ)

end EpGroupoid

/-! ### The example -/

namespace FaceMeetExample

open MPolyfold TameBoundaryExample EpGroupoid

variable (W : ScBanach)

/-- The coordinates of `[0,∞)³ ⊕ W` (Chapter 2's `TameBoundaryExample.coord`). -/
local notation "κ" => TameBoundaryExample.coord

local notation "continuous_κ" => TameBoundaryExample.continuous_coord

/-- `V = ([0,∞)³ ⊕ W) ∖ K`, `K = {p₀ + p₁ ≤ 1/4, 1 ≤ p₂ ≤ 2}`. -/
def V : Set (quadrant 3 W 0) :=
  {p | 1 / 4 < κ 0 p + κ 1 p ∨ κ 2 p < 1 ∨ 2 < κ 2 p}

theorem isOpen_V : IsOpen (V W) :=
  (isOpen_lt continuous_const ((continuous_κ 0).add (continuous_κ 1))).union
    ((isOpen_lt (continuous_κ 2) continuous_const).union
      (isOpen_lt continuous_const (continuous_κ 2)))

theorem pt_mem_V {a b c : ℝ} (h : 1 / 4 < max a 0 + max b 0 ∨ max c 0 < 1 ∨ 2 < max c 0) :
    pt W a b c ∈ V W := h

instance : Nonempty (V W) := ⟨⟨pt W 0 0 0, pt_mem_V W (Or.inr (Or.inl (by norm_num)))⟩⟩

/-- The open subset `V` with Part I's structure `restrictOpen`. -/
abbrev PV : MPolyfold (V W) := (quadrantPolyfold 3 W).restrictOpen (isOpen_V W)

/-- The trivial ep-groupoid of `V`. -/
abbrev XV : EpGroupoid (V W) (V W) := trivial (PV W)

theorem isEpFaceStructured_XV : (XV W).IsEpFaceStructured :=
  isEpFaceStructured_trivial_restrictOpen _ _ (quadrantPolyfold_isTame 3 W)
    (isFaceStructuredOpen_quadrant (isOpen_V W))

/-- `π : V → |X|` as a homeomorphism. -/
def piH : V W ≃ₜ (XV W).OrbitSpace :=
  IsHomeomorph.homeomorph _ (Examples.isHomeomorph_π_trivial (PV W))

/-- The coordinates on `|X|`. -/
def cX (i : Fin 3) (z : (XV W).OrbitSpace) : ℝ := κ i ((piH W).symm z : quadrant 3 W 0)

variable {W}

theorem continuous_cX (i : Fin 3) : Continuous (cX W i) :=
  (continuous_κ i).comp (continuous_subtype_val.comp (piH W).symm.continuous)

theorem cX_π (i : Fin 3) (v : V W) : cX W i ((XV W).π v) = κ i (v : quadrant 3 W 0) := by
  have h : (piH W).symm ((XV W).π v) = v := (piH W).symm_apply_apply v
  simp only [cX, h]

theorem cX_nonneg (i : Fin 3) (z : (XV W).OrbitSpace) : 0 ≤ cX W i z :=
  TameBoundaryExample.coord_nonneg i _

/-- `d_{|X|}` counts the vanishing coordinates. -/
theorem degIndexOrbit_eq (z : (XV W).OrbitSpace) : (XV W).degIndexOrbit z =
    (if cX W 0 z = 0 then 1 else 0) + (if cX W 1 z = 0 then 1 else 0) +
      (if cX W 2 z = 0 then 1 else 0) := by
  obtain ⟨v, rfl⟩ := (XV W).surjective_π z
  rw [degIndexOrbit_π, cX_π, cX_π, cX_π]
  change (PV W).degIndex v = _
  exact (MPolyfold.degIndex_restrictOpen _ (isOpen_V W) v).trans (dq_three _)

/-- The path `t ↦ (0, t(3 − t), t)` in `V`. -/
def γ₀ (t : ℝ) : V W :=
  ⟨pt W 0 (t * (3 - t)) t, pt_mem_V W (by
    rcases lt_or_ge t 1 with h | h
    · exact Or.inr (Or.inl (max_lt h (by norm_num)))
    rcases lt_or_ge 2 t with h' | h'
    · exact Or.inr (Or.inr (lt_max_of_lt_left h'))
    · left
      have : 2 ≤ t * (3 - t) := by nlinarith
      have h2 : t * (3 - t) ≤ max (t * (3 - t)) 0 := le_max_left _ _
      have h3 : (0 : ℝ) ≤ max 0 0 := le_max_left _ _
      linarith)⟩

/-- The path `t ↦ (t(3 − t), 0, t)` in `V`. -/
def γ₁ (t : ℝ) : V W :=
  ⟨pt W (t * (3 - t)) 0 t, pt_mem_V W (by
    rcases lt_or_ge t 1 with h | h
    · exact Or.inr (Or.inl (max_lt h (by norm_num)))
    rcases lt_or_ge 2 t with h' | h'
    · exact Or.inr (Or.inr (lt_max_of_lt_left h'))
    · left
      have : 2 ≤ t * (3 - t) := by nlinarith
      have h2 : t * (3 - t) ≤ max (t * (3 - t)) 0 := le_max_left _ _
      have h3 : (0 : ℝ) ≤ max 0 0 := le_max_left _ _
      linarith)⟩

theorem continuous_γ₀ : Continuous (γ₀ (W := W)) :=
  (continuous_pt continuous_const (by fun_prop) continuous_id).subtype_mk _

theorem continuous_γ₁ : Continuous (γ₁ (W := W)) :=
  (continuous_pt (by fun_prop) continuous_const continuous_id).subtype_mk _

theorem γ₁_zero : γ₁ (W := W) 0 = γ₀ 0 :=
  Subtype.ext <| Subtype.ext <| Prod.ext (funext fun i => by fin_cases i <;> simp [γ₀, γ₁, pt]) rfl

theorem γ₁_three : γ₁ (W := W) 3 = γ₀ 3 :=
  Subtype.ext <| Subtype.ext <| Prod.ext (funext fun i => by fin_cases i <;> simp [γ₀, γ₁, pt]) rfl

theorem degIndexOrbit_γ₀ {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 3) :
    (XV W).degIndexOrbit ((XV W).π (γ₀ t)) = 1 := by
  have h1 : 0 < t * (3 - t) := mul_pos ht.1 (by linarith [ht.2])
  rw [degIndexOrbit_eq, cX_π, cX_π, cX_π]
  simp [γ₀, max_eq_left h1.le, max_eq_left ht.1.le, h1.ne', ht.1.ne']

theorem degIndexOrbit_γ₁ {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 3) :
    (XV W).degIndexOrbit ((XV W).π (γ₁ t)) = 1 := by
  have h1 : 0 < t * (3 - t) := mul_pos ht.1 (by linarith [ht.2])
  rw [degIndexOrbit_eq, cX_π, cX_π, cX_π]
  simp [γ₁, max_eq_left h1.le, max_eq_left ht.1.le, h1.ne', ht.1.ne']

/-- A path through `{d_{|X|} = 1}` on `(0, 3)`: its ends lie in the face through `c(1)`. -/
theorem mem_face_of_path {c : ℝ → V W} (hc : Continuous c)
    (h1 : ∀ t ∈ Ioo (0 : ℝ) 3, (XV W).degIndexOrbit ((XV W).π (c t)) = 1) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 3) :
    (XV W).π (c s) ∈
      closure (connectedComponentIn {w | (XV W).degIndexOrbit w = 1} ((XV W).π (c 1))) := by
  have hcont : Continuous fun t => (XV W).π (c t) := (XV W).continuous_π.comp hc
  have hsub : (fun t => (XV W).π (c t)) '' Ioo 0 3 ⊆
      connectedComponentIn {w | (XV W).degIndexOrbit w = 1} ((XV W).π (c 1)) := by
    refine (isPreconnected_Ioo.image _ hcont.continuousOn).subset_connectedComponentIn
      ⟨1, ⟨by norm_num, by norm_num⟩, rfl⟩ ?_
    rintro _ ⟨t, ht, rfl⟩
    exact h1 t ht
  refine closure_mono hsub ?_
  have hs' : s ∈ closure (Ioo (0 : ℝ) 3) := by rw [closure_Ioo (by norm_num)]; exact hs
  exact hcont.continuousWithinAt.mem_closure_image hs'

/-- The face `θ = closure of the component of `{d_{|X|} = 1}` through `(0, 2, 1)` (the face
`V ∩ {p₀ = 0}`). -/
def θ₀ : Set (XV W).OrbitSpace :=
  closure (connectedComponentIn {w | (XV W).degIndexOrbit w = 1} ((XV W).π (γ₀ 1)))

/-- The face through `(2, 0, 1)` (the face `V ∩ {p₁ = 0}`). -/
def θ₁ : Set (XV W).OrbitSpace :=
  closure (connectedComponentIn {w | (XV W).degIndexOrbit w = 1} ((XV W).π (γ₁ 1)))

theorem isOrbitFace_θ₀ : (XV W).IsOrbitFace θ₀ :=
  ⟨_, degIndexOrbit_γ₀ ⟨by norm_num, by norm_num⟩, rfl⟩

theorem isOrbitFace_θ₁ : (XV W).IsOrbitFace θ₁ :=
  ⟨_, degIndexOrbit_γ₁ ⟨by norm_num, by norm_num⟩, rfl⟩

theorem γ₀_mem_θ₀ {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 3) : (XV W).π (γ₀ s) ∈ θ₀ :=
  mem_face_of_path continuous_γ₀ (fun _ ht => degIndexOrbit_γ₀ ht) hs

theorem γ₁_mem_θ₁ {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 3) : (XV W).π (γ₁ s) ∈ θ₁ :=
  mem_face_of_path continuous_γ₁ (fun _ ht => degIndexOrbit_γ₁ ht) hs

/-- `θ₀` lies in `{p₀ = 0}`: the component lies in the open set `{p₁ > 0, p₂ > 0}`, separated
inside `{d = 1}` from `{p₀ > 0}`. -/
theorem cX_zero_of_mem_θ₀ {z : (XV W).OrbitSpace} (hz : z ∈ θ₀) : cX W 0 z = 0 := by
  set S := connectedComponentIn {w | (XV W).degIndexOrbit w = 1} ((XV W).π (γ₀ 1)) with hS
  have hS1 : ∀ w ∈ S, (XV W).degIndexOrbit w = 1 := fun w hw =>
    connectedComponentIn_subset {w | (XV W).degIndexOrbit w = 1} _ hw
  set u := {w | 0 < cX W 1 w ∧ 0 < cX W 2 w}
  set v := {w | 0 < cX W 0 w}
  have hu : IsOpen u := (isOpen_lt continuous_const (continuous_cX 1)).inter
    (isOpen_lt continuous_const (continuous_cX 2))
  have hv : IsOpen v := isOpen_lt continuous_const (continuous_cX 0)
  have hpos : ∀ i w, cX W i w ≠ 0 → 0 < cX W i w := fun i w h => lt_of_le_of_ne (cX_nonneg i w)
    (Ne.symm h)
  have hcover : S ⊆ u ∪ v := by
    intro w hw
    have h := hS1 w hw
    rw [degIndexOrbit_eq] at h
    by_cases h0 : cX W 0 w = 0
    · left
      by_cases h1 : cX W 1 w = 0 <;> by_cases h2 : cX W 2 w = 0 <;> simp [h0, h1, h2] at h
      exact ⟨hpos 1 w h1, hpos 2 w h2⟩
    · exact Or.inr (hpos 0 w h0)
  have hdisj : S ∩ (u ∩ v) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun w ⟨hw, ⟨h1, h2⟩, h0⟩ => ?_
    have h := hS1 w hw
    rw [degIndexOrbit_eq] at h
    simp [(show 0 < cX W 0 w from h0).ne', h1.ne', h2.ne'] at h
  have hmem : (XV W).π (γ₀ 1) ∈ S := mem_connectedComponentIn (degIndexOrbit_γ₀
    ⟨by norm_num, by norm_num⟩)
  have h0 : cX W 0 ((XV W).π (γ₀ 1)) = 0 := by
    rw [cX_π]; simp [γ₀]
  have hSu : S ⊆ u := by
    rcases (isPreconnected_iff_subset_of_disjoint.1 isPreconnected_connectedComponentIn) u v hu hv
      hcover hdisj with h | h
    · exact h
    · exact absurd (h hmem) (by simp [v, h0])
  have hS0 : S ⊆ {w | cX W 0 w = 0} := by
    intro w hw
    obtain ⟨h1, h2⟩ := hSu hw
    have h := hS1 w hw
    rw [degIndexOrbit_eq] at h
    by_contra h0
    have h0' : cX W 0 w ≠ 0 := h0
    simp [h0', h1.ne', h2.ne'] at h
  exact closure_minimal hS0 (isClosed_eq (continuous_cX 0) continuous_const) hz

theorem θ₀_ne_θ₁ : (θ₀ : Set (XV W).OrbitSpace) ≠ θ₁ := by
  intro h
  have hm : (XV W).π (γ₁ 1) ∈ θ₀ := h ▸ γ₁_mem_θ₁ ⟨by norm_num, by norm_num⟩
  have := cX_zero_of_mem_θ₀ hm
  rw [cX_π] at this
  norm_num [γ₁] at this

/-! ### The face `X_θ₀` and its faces -/

/-- The face `X_θ₀` as an ep-groupoid (Proposition 11.1.6). -/
abbrev F₀ := faceEpGroupoid (isEpFaceStructured_XV W) isOrbitFace_θ₀

/-- The height `p₂` on `|X_θ₀|`, through the orbit map of the inclusion `X_θ₀ → X`. -/
def cF (z : (F₀ (W := W)).OrbitSpace) : ℝ :=
  cX W 2 ((subEpFunctor (isEpSubgroupoid_faceObj (isEpFaceStructured_XV W)
    isOrbitFace_θ₀)).orbitMap z)

theorem continuous_cF : Continuous (cF (W := W)) :=
  (continuous_cX 2).comp (EpFunctor.continuous_orbitMap _)

theorem cF_π (x : (XV W).faceObj θ₀) :
    cF ((F₀ (W := W)).π x) = κ 2 ((x : V W) : quadrant 3 W 0) :=
  cX_π 2 x.1

/-- The points of `X_θ₀` with `d_{X_θ₀} = 1` have height `< 1` or `> 2`: they lie on the edge
`p₀ = p₂ = 0` or on the edge `p₀ = p₁ = 0` outside `K`. -/
theorem cF_lt_or_gt {w : (F₀ (W := W)).OrbitSpace} (hw : (F₀ (W := W)).degIndexOrbit w = 1) :
    cF w < 1 ∨ 2 < cF w := by
  obtain ⟨x, rfl⟩ := (F₀ (W := W)).surjective_π w
  have hd : (XV W).PObj.degIndex x = 2 := by
    rw [degIndex_faceEpGroupoid (isEpFaceStructured_XV W) isOrbitFace_θ₀ x]
    have : (F₀ (W := W)).PObj.degIndex x = 1 := hw
    rw [this]
  have hd' : (XV W).degIndexOrbit ((XV W).π x) = 2 := hd
  have h0 : cX W 0 ((XV W).π x) = 0 := cX_zero_of_mem_θ₀ x.2
  rw [degIndexOrbit_eq, h0] at hd'
  have hV := (x : V W).2
  rw [cF_π]
  rw [cX_π] at h0 hd'
  rw [cX_π] at hd'
  by_cases h2 : κ 2 ((x : V W) : quadrant 3 W 0) = 0
  · left; rw [h2]; norm_num
  · have h1 : κ 1 ((x : V W) : quadrant 3 W 0) = 0 := by
      by_contra h1; simp [h1, h2] at hd'
    rcases hV with h | h | h
    · rw [h0, h1] at h; norm_num at h
    · exact Or.inl h
    · exact Or.inr h

/-- The points `(0, 0, 0)` and `(0, 0, 3)` of `X_θ₀ ∩ X_θ₁`. -/
def xs (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 3) : (XV W).faceObj θ₀ := ⟨γ₀ s, γ₀_mem_θ₀ hs⟩

theorem xs_mem_θ₁ {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 3) (h : γ₁ (W := W) s = γ₀ s) :
    (xs s hs).1 ∈ (XV W).faceObj θ₁ := by
  change (XV W).π (γ₀ s) ∈ θ₁
  rw [← h]
  exact γ₁_mem_θ₁ hs

theorem cF_xs (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 3) : cF ((F₀ (W := W)).π (xs s hs)) = s := by
  rw [cF_π]
  simp [xs, γ₀, max_eq_left hs.1]

/-- `X_θ₀ ∩ X_θ₁` is not a face of `X_θ₀`: a face is the closure of one component `S` of
`{d_{|X_θ₀|} = 1}`, which lies in `{p₂ < 1}` or in `{p₂ > 2}`, and its closure cannot contain
both `(0, 0, 0)` and `(0, 0, 3)`. -/
theorem not_isEpFace_inter :
    ¬ (F₀ (W := W)).IsEpFace (Subtype.val ⁻¹' (XV W).faceObj θ₁) := by
  rintro ⟨θ'', ⟨z, -, rfl⟩, hA⟩
  have hm : ∀ (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 3), γ₁ (W := W) s = γ₀ s →
      (F₀ (W := W)).π (xs s hs) ∈
        closure (connectedComponentIn {w | (F₀ (W := W)).degIndexOrbit w = 1} z) := by
    intro s hs h
    have : xs s hs ∈ (Subtype.val ⁻¹' (XV W).faceObj θ₁ : Set ((XV W).faceObj θ₀)) :=
      xs_mem_θ₁ hs h
    rw [hA] at this
    exact this
  obtain ⟨w₀, hw₀, e₀⟩ : ∃ w ∈ closure (connectedComponentIn
      {w | (F₀ (W := W)).degIndexOrbit w = 1} z), cF w = 0 :=
    ⟨_, hm 0 ⟨le_rfl, by norm_num⟩ γ₁_zero, cF_xs 0 _⟩
  obtain ⟨w₃, hw₃, e₃⟩ : ∃ w ∈ closure (connectedComponentIn
      {w | (F₀ (W := W)).degIndexOrbit w = 1} z), cF w = 3 :=
    ⟨_, hm 3 ⟨by norm_num, le_rfl⟩ γ₁_three, cF_xs 3 _⟩
  have hcover : connectedComponentIn {w | (F₀ (W := W)).degIndexOrbit w = 1} z ⊆
      {w | cF w < 1} ∪ {w | 2 < cF w} := fun w hw =>
    cF_lt_or_gt (connectedComponentIn_subset {w | (F₀ (W := W)).degIndexOrbit w = 1} _ hw)
  have hdisj : Disjoint {w : (F₀ (W := W)).OrbitSpace | cF w < 1} {w | 2 < cF w} :=
    disjoint_left.2 fun w h1 h2 => by
      have h1' : cF w < 1 := h1
      have h2' : 2 < cF w := h2
      linarith
  rcases isPreconnected_connectedComponentIn.subset_or_subset
      (isOpen_lt continuous_cF continuous_const) (isOpen_lt continuous_const continuous_cF)
      hdisj hcover with h | h
  · have h' : cF w₃ ≤ 1 := closure_lt_subset_le continuous_cF continuous_const (closure_mono h hw₃)
    linarith
  · have h' : 2 ≤ cF w₀ := closure_lt_subset_le continuous_const continuous_cF (closure_mono h hw₀)
    linarith

/-- **2021 Proposition 11.1.6, p. 524 (2017: Proposition 11.2, p. 378): the intersection clause
does not hold as we read it.**  The trivial ep-groupoid of `V = ([0,∞)³ ⊕ W) ∖ K`,
`K = {p₀ + p₁ ≤ 1/4, 1 ≤ p₂ ≤ 2}`, is face structured; its faces `X_θ₀ = V ∩ {p₀ = 0}` and
`X_θ₁ = V ∩ {p₁ = 0}` are distinct and meet (at the origin), but `X_θ₀ ∩ X_θ₁` is not a face
of the ep-groupoid `X_θ₀`. -/
theorem not_facesMeetInFaces : ¬ FacesMeetInFaces (XV W) (isEpFaceStructured_XV W) := by
  intro h
  exact not_isEpFace_inter (h θ₀ θ₁ isOrbitFace_θ₀ isOrbitFace_θ₁ θ₀_ne_θ₁
    ⟨γ₀ 0, γ₀_mem_θ₀ ⟨le_rfl, by norm_num⟩,
      by change (XV W).π (γ₀ 0) ∈ θ₁; rw [← γ₁_zero]; exact γ₁_mem_θ₁ ⟨le_rfl, by norm_num⟩⟩).1

end FaceMeetExample

end Polyfold
