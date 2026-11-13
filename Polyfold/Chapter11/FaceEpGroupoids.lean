import Polyfold.Chapter11.EpEquivalenceGeometryFaces
import Polyfold.Chapter7.SubGroupoid

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.1: **Proposition 11.1.6** (2021 pp. 524–525; 2017: Proposition 11.2,
p. 378), the first part: faces of a face structured tame ep-groupoid are tame ep-groupoids.

# Faces of a face structured ep-groupoid as ep-groupoids

## The text, paraphrased

(Proposition 11.1.6) If the tame ep-groupoid `X` is face structured, the object set of each face
`F = X_θ` is a sub-M-polyfold of `X` with tame induced structure, likewise the morphism set,
and `F` with the induced structures is an ep-groupoid.  *Proof* (pp. 524–525): a point `x ∈ X_θ`
lies in `d_X(x)` local faces; if it lay in fewer global faces of the object M-polyfold, fewer
faces of `|X|` would pass through `|x|`.  So `x ∈ X_θ` lies in exactly one global face `F ⊆ X_θ`
of the object M-polyfold; `X_θ` is a disjoint union of such faces, which are sub-M-polyfolds
with tame induced structure (Theorem 2.5.17), so `X_θ` is a sub-M-polyfold and the full
subcategory is an ep-groupoid.

## What is formalized

* `EpGroupoid.image_faceAt_subset`: `π` maps the face of the object M-polyfold through `p` into
  the face of `|X|` through `|p|`.
* For local pieces `L` of `{d_X = 1}` at `x` (Chapter 2's `LocalPieces`):
  `orbitFacesThrough_eq_range` (the faces of `|X|` through `|x|` are those through the images
  of the pieces), `injective_orbitFaceAt_pt` (injective when `X` is face structured),
  `injective_faceAt_pt`.
* `IsEpFaceStructured.isWeaklyFaceStructured`: an (ep-)face structured tame ep-groupoid is
  weakly face structured (the first step of the text's proof).
* `IsEpFaceStructured.existsUnique_face_subset`: every `x ∈ X_θ` lies in exactly one face of
  the object M-polyfold contained in `X_θ`; `IsEpFaceStructured.exists_nhds_eq_face`: near `x`,
  `X_θ` is that face.
* `MPolyfold.isSubMPolyfold_of_forall_nhds` (a set that near each of its points agrees with a
  sub-M-polyfold is one), `MPolyfold.isScDiffeoOn_subPolyfold_of_inter_eq` (two sub-M-polyfolds
  agreeing on an open `U` have sc-diffeomorphic open pieces over `U`).
* **Proposition 11.1.6, first part**: `isSubMPolyfold_faceObj`, `isEpSubgroupoid_faceObj`,
  `isClosed_faceObj`, `faceEpGroupoid` (the face `X_θ` as an ep-groupoid, Proposition
  7.1.22's `subEpGroupoid`), `isTame_faceEpGroupoid` (tame induced structure on the objects),
  `isTame_faceEpGroupoid_mor` (on the morphisms), `degIndex_faceEpGroupoid`
  (`d_X(x) = d_{X_θ}(x) + 1`), collected in `proposition_11_1_6_faces`.

## Choices

* The faces are taken in the ep-groupoid sense of Definition 11.1.3 (`X_θ`, `θ` a face of
  `|X|`), as in the text's statement; the text's proof passes through the faces of the object
  M-polyfold, and so does the formal proof.
* "Disjoint union" is read locally: near each of its points `X_θ` agrees with one face of the
  object M-polyfold (`exists_nhds_eq_face`), which is what the sub-M-polyfold property and the
  tameness of the induced structure need.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

open TameBoundary

universe u v

/-! ### Sub-M-polyfolds which agree on open sets -/

namespace MPolyfold

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {P : MPolyfold Z}

/-- A set that near each of its points agrees with a sub-M-polyfold is a sub-M-polyfold: the
retraction `r : V → V` onto `F ∩ V` restricts to `V' = (V ∩ U) ∩ r⁻¹(V ∩ U)`. -/
theorem isSubMPolyfold_of_forall_nhds {A : Set Z}
    (h : ∀ a ∈ A, ∃ F, P.IsSubMPolyfold F ∧ ∃ U, IsOpen U ∧ a ∈ U ∧ A ∩ U = F ∩ U) :
    P.IsSubMPolyfold A := by
  intro a ha
  obtain ⟨F, hF, U, hU, haU, hAU⟩ := h a ha
  have haF : a ∈ F := (hAU.subset ⟨ha, haU⟩).1
  obtain ⟨V, hV, haV, r, hmaps, hsm, hidem, himg⟩ := hF a haF
  have hfix : ∀ y ∈ F ∩ V, r y = y := fun y hy => by
    rw [← himg] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact hidem z hz
  set V' := (V ∩ U) ∩ r ⁻¹' (V ∩ U) with hV'
  have hV'o : IsOpen V' :=
    (hsm.continuousOn.mono inter_subset_left).isOpen_inter_preimage (hV.inter hU) (hV.inter hU)
  have hmaps' : MapsTo r V' V' := fun y hy => ⟨hy.2, by
    rw [mem_preimage, hidem y hy.1.1]; exact hy.2⟩
  refine ⟨V', hV'o, ⟨⟨haV, haU⟩, ?_⟩, r, hmaps', hsm.mono hV'o fun y hy => hy.1.1,
    fun y hy => hidem y hy.1.1, ?_⟩
  · rw [mem_preimage, hfix a ⟨haF, haV⟩]; exact ⟨haV, haU⟩
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzF : r z ∈ F := (himg ▸ mem_image_of_mem r hz.1.1 : r z ∈ F ∩ V).1
      have hzU : r z ∈ U := hz.2.2
      exact ⟨(hAU.symm.subset ⟨hzF, hzU⟩).1, hmaps' hz⟩
    · rintro ⟨hyA, hy⟩
      have hyF : y ∈ F := (hAU.subset ⟨hyA, hy.1.2⟩).1
      exact ⟨y, hy, hfix y ⟨hyF, hy.1.1⟩⟩

/-- A map into a sub-M-polyfold `A ⊆ Z` is sc-smooth into `A` as soon as it is sc-smooth into
`Z` (Proposition 2.3.19 (2); the argument of Chapter 7's `SubGroupoid.lean`). -/
theorem isScSmoothOn_sub_of_val {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    [ParacompactSpace Y] {Q : MPolyfold Y} {A : Set Z} (hA : P.IsSubMPolyfold A)
    [ParacompactSpace A] {f : Y → A} {U : Set Y}
    (hf : Q.IsScSmoothOn P (fun y => (f y : Z)) U) :
    Q.IsScSmoothOn (subPolyfold hA) f U := by
  refine IsScSmoothOn.of_locally hf.isOpen fun x hx => ?_
  set d := hA.data (f x).2
  have hU' : IsOpen (U ∩ (fun y => (f y : Z)) ⁻¹' d.V) :=
    hf.continuousOn.isOpen_inter_preimage hf.isOpen d.isOpen
  refine ⟨_, hU', ⟨hx, hA.mem_data_V (f x).2⟩, inter_subset_left, ?_⟩
  refine (IsScSmoothOn.comp (subPolyfold_retraction_isScSmooth hA d (f x))
    (hf.mono hU' inter_subset_left) fun y hy => hy.2).congr fun y hy => Subtype.ext ?_
  simp only [Function.comp_apply]
  rw [d.retractInto_val (f x) hy.2]
  exact d.apply_eq_self ⟨(f y).2, hy.2⟩

open scoped Classical in
/-- The map `F → A`, `y ↦ y` where `y ∈ A`, with a junk value elsewhere. -/
def subIncl {A F : Set Z} (a₀ : A) (y : F) : A :=
  if h : (y : Z) ∈ A then ⟨y, h⟩ else a₀

omit [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] in
theorem subIncl_val {A F : Set Z} (a₀ : A) {y : F} (h : (y : Z) ∈ A) :
    (subIncl a₀ y : Z) = y := by
  classical
  rw [subIncl, dif_pos h]

/-- **Two sub-M-polyfolds which agree on an open set `U`** have sc-diffeomorphic open pieces
over `U`: the identity of `A ∩ U = F ∩ U`. -/
theorem isScDiffeoOn_subPolyfold_of_inter_eq {A F : Set Z} (hA : P.IsSubMPolyfold A)
    (hF : P.IsSubMPolyfold F) [ParacompactSpace A] [ParacompactSpace F] {U : Set Z}
    (hU : IsOpen U) (hAU : A ∩ U = F ∩ U) (a₀ : A) (f₀ : F) :
    (subPolyfold hA).IsScDiffeoOn (subPolyfold hF) (subIncl f₀) (subIncl a₀)
      (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' U) := by
  have hAF : ∀ a : A, (a : Z) ∈ U → (a : Z) ∈ F := fun a ha =>
    (hAU.subset ⟨a.2, ha⟩).1
  have hFA : ∀ y : F, (y : Z) ∈ U → (y : Z) ∈ A := fun y hy =>
    (hAU.symm.subset ⟨y.2, hy⟩).1
  have hoA : IsOpen (Subtype.val ⁻¹' U : Set A) := hU.preimage continuous_subtype_val
  have hoF : IsOpen (Subtype.val ⁻¹' U : Set F) := hU.preimage continuous_subtype_val
  refine ⟨?_, ?_, fun a ha => ?_, fun y hy => ?_, fun a ha => ?_, fun y hy => ?_⟩
  · refine isScSmoothOn_sub_of_val hF ?_
    exact ((subPolyfold_inclusion_isScSmooth hA).mono hoA (subset_univ _)).congr
      fun a ha => (subIncl_val f₀ (hAF a ha)).symm
  · refine isScSmoothOn_sub_of_val hA ?_
    exact ((subPolyfold_inclusion_isScSmooth hF).mono hoF (subset_univ _)).congr
      fun y hy => (subIncl_val a₀ (hFA y hy)).symm
  · change ((subIncl f₀ a : F) : Z) ∈ U
    rw [subIncl_val f₀ (hAF a ha)]; exact ha
  · change ((subIncl a₀ y : A) : Z) ∈ U
    rw [subIncl_val a₀ (hFA y hy)]; exact hy
  · have h1 : ((subIncl f₀ a : F) : Z) = a := subIncl_val f₀ (hAF a ha)
    refine Subtype.ext ?_
    rw [subIncl_val a₀ (by rw [h1]; exact a.2), h1]
  · have h1 : ((subIncl a₀ y : A) : Z) = y := subIncl_val a₀ (hFA y hy)
    refine Subtype.ext ?_
    rw [subIncl_val f₀ (by rw [h1]; exact y.2), h1]

end MPolyfold

/-! ### Faces of the object M-polyfold and faces of `|X|` -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- `π` maps a connected component of `{d_X = 1}` into a connected component of
`{d_{|X|} = 1}`. -/
theorem image_cc_subset (p : Obj) :
    X.π '' connectedComponentIn (univ ∩ {z | X.PObj.degIndex z = 1}) p ⊆
      connectedComponentIn (univ ∩ {w | X.degIndexOrbit w = 1}) (X.π p) := by
  by_cases hp : p ∈ univ ∩ {z | X.PObj.degIndex z = 1}
  · refine (isPreconnected_connectedComponentIn.image _
      X.continuous_π.continuousOn).subset_connectedComponentIn
      (mem_image_of_mem _ (mem_connectedComponentIn hp)) ?_
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨mem_univ _, (connectedComponentIn_subset _ _ hz).2⟩
  · rw [connectedComponentIn_eq_empty hp, image_empty]
    exact empty_subset _

/-- `π` maps the face of the object M-polyfold through `p` into the face of `|X|` through
`|p|`. -/
theorem image_faceAt_subset (p : Obj) :
    X.π '' faceAt X.PObj.degIndex univ p ⊆ faceAt X.degIndexOrbit univ (X.π p) := by
  rintro _ ⟨y, ⟨-, hy⟩, rfl⟩
  exact ⟨mem_univ _, closure_mono (X.image_cc_subset p)
    (image_closure_subset_closure_image X.continuous_π (mem_image_of_mem _ hy))⟩

variable {X}

/-- In `|X|`, a point with `d_{|X|} = 1` in the closure of a component of `{d_{|X|} = 1}` lies in
that component (the single local piece at a preimage maps into it). -/
theorem mem_cc_of_mem_closure_orbit (hd : IsCornerIndex X.PObj.degIndex) {q w : X.OrbitSpace}
    (hq : X.degIndexOrbit q = 1)
    (hqw : q ∈ closure (connectedComponentIn (univ ∩ {z | X.degIndexOrbit z = 1}) w)) :
    q ∈ connectedComponentIn (univ ∩ {z | X.degIndexOrbit z = 1}) w := by
  obtain ⟨y, rfl⟩ := X.surjective_π q
  obtain ⟨L⟩ := hd.exists_localPieces (univ_mem : (univ : Set Obj) ∈ 𝓝 y)
  have hy1 : X.PObj.degIndex y = 1 := hq
  obtain ⟨_, ⟨g, hgB, rfl⟩, hgG⟩ := mem_closure_iff.1 hqw (X.π '' L.B)
    (X.proposition_7_1_8 _ L.isOpen_B) (mem_image_of_mem _ L.mem_B)
  have hg1 : X.PObj.degIndex g = 1 := (connectedComponentIn_subset _ _ hgG).2
  obtain ⟨i, hgi⟩ := mem_iUnion.1 (L.cover ⟨hgB, hg1⟩)
  obtain ⟨j, hyj⟩ := mem_iUnion.1 (L.cover ⟨L.mem_B, hy1⟩)
  have hij : i = j := by
    have h1 := i.isLt; have h2 := j.isLt
    ext; omega
  subst hij
  have hsub : X.π '' L.piece i ⊆ connectedComponentIn (univ ∩ {z | X.degIndexOrbit z = 1}) w := by
    rw [connectedComponentIn_eq hgG]
    refine ((L.isPreconnected i).image _ X.continuous_π.continuousOn).subset_connectedComponentIn
      (mem_image_of_mem _ hgi) ?_
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨mem_univ _, (L.piece_subset i hz).2⟩
  exact hsub (mem_image_of_mem _ hyj)

/-- A face of `|X|` through a point `q` with `d_{|X|}(q) = 1` is the face of `q`. -/
theorem faceAt_orbit_eq_of_mem (hd : IsCornerIndex X.PObj.degIndex) {q w : X.OrbitSpace}
    (hq : X.degIndexOrbit q = 1) (hqw : q ∈ faceAt X.degIndexOrbit univ w) :
    faceAt X.degIndexOrbit univ w = faceAt X.degIndexOrbit univ q := by
  unfold faceAt
  rw [connectedComponentIn_eq (mem_cc_of_mem_closure_orbit hd hq hqw.2)]

section Pieces

variable {x : Obj} (L : LocalPieces X.PObj.degIndex x univ)

theorem degIndex_pt (i : Fin (X.PObj.degIndex x)) : X.PObj.degIndex (L.pt i) = 1 :=
  (L.piece_subset i (L.pt_mem i)).2

theorem mem_orbitFaceAt_pt (i : Fin (X.PObj.degIndex x)) :
    X.π x ∈ faceAt X.degIndexOrbit univ (X.π (L.pt i)) :=
  X.image_faceAt_subset _ (mem_image_of_mem _ (L.mem_faceAt_pt (mem_univ x) i))

/-- Every face of `|X|` through `|x|` is the face through the image of one of the local
pieces at `x`. -/
theorem exists_eq_orbitFaceAt_pt {θ : Set X.OrbitSpace} (hθ : X.IsOrbitFace θ)
    (hx : X.π x ∈ θ) : ∃ i, θ = faceAt X.degIndexOrbit univ (X.π (L.pt i)) := by
  obtain ⟨q, -, hq1, rfl⟩ := EpGroupoid.isOrbitFace_iff_isFaceIn.1 hθ
  obtain ⟨_, ⟨g, hgB, rfl⟩, hgG⟩ := mem_closure_iff.1 hx.2 (X.π '' L.B)
    (X.proposition_7_1_8 _ L.isOpen_B) (mem_image_of_mem _ L.mem_B)
  have hg1 : X.PObj.degIndex g = 1 := (connectedComponentIn_subset _ _ hgG).2
  obtain ⟨i, hgi⟩ := mem_iUnion.1 (L.cover ⟨hgB, hg1⟩)
  have hsub : X.π '' L.piece i ⊆ connectedComponentIn (univ ∩ {z | X.degIndexOrbit z = 1}) q := by
    rw [connectedComponentIn_eq hgG]
    refine ((L.isPreconnected i).image _ X.continuous_π.continuousOn).subset_connectedComponentIn
      (mem_image_of_mem _ hgi) ?_
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨mem_univ _, (L.piece_subset i hz).2⟩
  refine ⟨i, ?_⟩
  unfold faceAt
  rw [connectedComponentIn_eq (hsub (mem_image_of_mem _ (L.pt_mem i)))]

/-- The faces of `|X|` through `|x|` are the faces through the images of the local pieces. -/
theorem orbitFacesThrough_eq_range :
    X.orbitFacesThrough (X.π x) = range fun i => faceAt X.degIndexOrbit univ (X.π (L.pt i)) := by
  ext θ
  constructor
  · rintro ⟨hθ, hx⟩
    obtain ⟨i, rfl⟩ := exists_eq_orbitFaceAt_pt L hθ hx
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨EpGroupoid.isOrbitFace_iff_isFaceIn.2 (isFaceIn_faceAt (mem_univ _) (degIndex_pt L i)),
      mem_orbitFaceAt_pt L i⟩

/-- For face structured `X`, the faces of `|X|` through the images of the local pieces are
distinct. -/
theorem injective_orbitFaceAt_pt (hX : X.IsEpFaceStructured) :
    Injective fun i => faceAt X.degIndexOrbit univ (X.π (L.pt i)) := by
  refine injective_of_encard_range_eq _ ?_
  rw [← orbitFacesThrough_eq_range L, hX.2]
  rfl

/-- For face structured `X`, the faces of the object M-polyfold through the local pieces are
distinct. -/
theorem injective_faceAt_pt (hd : IsCornerIndex X.PObj.degIndex) (hX : X.IsEpFaceStructured) :
    Injective fun i => faceAt X.PObj.degIndex univ (L.pt i) := by
  intro i j hij
  refine injective_orbitFaceAt_pt L hX ?_
  have hj := (faceAt_eq_faceAt_iff hd isOpen_univ (mem_univ (L.pt j)) (degIndex_pt L j)).1 hij
  change faceAt _ univ (X.π (L.pt i)) = faceAt _ univ (X.π (L.pt j))
  unfold faceAt
  rw [connectedComponentIn_eq (X.image_cc_subset _ (mem_image_of_mem _ hj))]

end Pieces

/-- **A face structured tame ep-groupoid is weakly face structured** (the first step of the
proof of Proposition 11.1.6, 2021 pp. 524–525): every `x` lies in exactly `d_X(x)` faces of the
object M-polyfold. -/
theorem IsEpFaceStructured.isWeaklyFaceStructured (hX : X.IsEpFaceStructured) :
    X.IsWeaklyFaceStructured := by
  have hd := MPolyfold.isCornerIndex_degIndex X.PObj hX.1
  refine ⟨hX.1, fun x => ?_⟩
  obtain ⟨L⟩ := hd.exists_localPieces (univ_mem : (univ : Set Obj) ∈ 𝓝 x)
  have h := (L.encard_facesThrough_eq_iff hd isOpen_univ (mem_univ x)).2
    (injective_faceAt_pt L hd hX)
  have he : {F : Set Obj | X.PObj.IsFace F ∧ x ∈ F} = facesThrough X.PObj.degIndex univ x := by
    ext F
    exact and_congr_left' X.PObj.isFaceIn_univ_iff.symm
  rw [he, h]

/-- **Every `x ∈ X_θ` lies in exactly one face of the object M-polyfold contained in `X_θ`**
(2021 p. 525: "an object `x ∈ X_θ` lies in precisely one global face `F` … so that
`F ⊂ X_θ`"). -/
theorem IsEpFaceStructured.existsUnique_face_subset (hX : X.IsEpFaceStructured)
    {θ : Set X.OrbitSpace} (hθ : X.IsOrbitFace θ) {x : Obj} (hx : x ∈ X.faceObj θ) :
    ∃ F, IsFaceIn X.PObj.degIndex univ F ∧ x ∈ F ∧ F ⊆ X.faceObj θ ∧
      ∀ F', IsFaceIn X.PObj.degIndex univ F' → x ∈ F' → F' ⊆ X.faceObj θ → F' = F := by
  have hd := MPolyfold.isCornerIndex_degIndex X.PObj hX.1
  obtain ⟨L⟩ := hd.exists_localPieces (univ_mem : (univ : Set Obj) ∈ 𝓝 x)
  obtain ⟨i, hi⟩ := exists_eq_orbitFaceAt_pt L hθ hx
  refine ⟨faceAt X.PObj.degIndex univ (L.pt i),
    isFaceIn_faceAt (mem_univ _) (degIndex_pt L i), L.mem_faceAt_pt (mem_univ x) i, ?_, ?_⟩
  · intro y hy
    change X.π y ∈ θ
    rw [hi]
    exact X.image_faceAt_subset _ (mem_image_of_mem _ hy)
  · intro F' hF' hxF' hF'θ
    have hmem : F' ∈ facesThrough X.PObj.degIndex univ x := ⟨hF', hxF'⟩
    rw [L.facesThrough_eq hd isOpen_univ (mem_univ x)] at hmem
    obtain ⟨j, rfl⟩ := hmem
    have hj : X.π (L.pt j) ∈ θ :=
      hF'θ (mem_faceAt_self (mem_univ _) (degIndex_pt L j))
    rw [hi] at hj
    have hji : j = i := injective_orbitFaceAt_pt L hX
      (faceAt_orbit_eq_of_mem hd (q := X.π (L.pt j)) (degIndex_pt L j) hj).symm
    rw [hji]

/-- **Near each of its points, `X_θ` is a single face of the object M-polyfold**: for the face
`F ⊆ X_θ` through `x` there is an open `U ∋ x` with `X_θ ∩ U = F ∩ U`. -/
theorem IsEpFaceStructured.exists_nhds_eq_face (hX : X.IsEpFaceStructured)
    {θ : Set X.OrbitSpace} (hθ : X.IsOrbitFace θ) {x : Obj} (hx : x ∈ X.faceObj θ) :
    ∃ F, X.PObj.IsFace F ∧ x ∈ F ∧ F ⊆ X.faceObj θ ∧
      ∃ U, IsOpen U ∧ x ∈ U ∧ X.faceObj θ ∩ U = F ∩ U := by
  have hd := MPolyfold.isCornerIndex_degIndex X.PObj hX.1
  obtain ⟨L⟩ := hd.exists_localPieces (univ_mem : (univ : Set Obj) ∈ 𝓝 x)
  obtain ⟨F, hF, hxF, hFθ, huniq⟩ := hX.existsUnique_face_subset hθ hx
  refine ⟨F, X.PObj.isFaceIn_univ_iff.1 hF, hxF, hFθ, L.B, L.isOpen_B, L.mem_B, ?_⟩
  refine Subset.antisymm (fun y hy => ⟨?_, hy.2⟩) fun y hy => ⟨hFθ hy.1, hy.2⟩
  obtain ⟨Fy, hFy, hyFy, hFyθ, -⟩ := hX.existsUnique_face_subset hθ hy.1
  have hxFy : x ∈ Fy :=
    (L.facesThrough_subset (mem_univ x) hy.2 (⟨hFy, hyFy⟩ : Fy ∈ facesThrough _ univ y)).2
  rw [← huniq Fy hFy hxFy hFyθ]
  exact hyFy

/-! ### Proposition 11.1.6: the face `X_θ` as a tame ep-groupoid -/

variable {θ : Set X.OrbitSpace}

theorem isClosed_faceObj (hθ : X.IsOrbitFace θ) : IsClosed (X.faceObj θ) := by
  obtain ⟨z, -, rfl⟩ := hθ
  exact isClosed_closure.preimage X.continuous_π

/-- **Proposition 11.1.6**: the object set `X_θ` of a face is a sub-M-polyfold. -/
theorem isSubMPolyfold_faceObj (hX : X.IsEpFaceStructured) (hθ : X.IsOrbitFace θ) :
    X.PObj.IsSubMPolyfold (X.faceObj θ) := by
  have hfs := hX.isWeaklyFaceStructured.2
  refine MPolyfold.isSubMPolyfold_of_forall_nhds fun x hx => ?_
  obtain ⟨F, hF, -, -, U, hU, hxU, hFU⟩ := hX.exists_nhds_eq_face hθ hx
  exact ⟨F, MPolyfold.theorem_2_5_17_isSubMPolyfold_face X.PObj hX.1 hfs hF, U, hU, hxU, hFU⟩

/-- `X_θ` is an ep-subgroupoid (Definition 7.1.21): a saturated sub-M-polyfold. -/
theorem isEpSubgroupoid_faceObj (hX : X.IsEpFaceStructured) (hθ : X.IsOrbitFace θ) :
    X.IsEpSubgroupoid (X.faceObj θ) :=
  ⟨isSubMPolyfold_faceObj hX hθ, isSaturated_faceObj θ⟩

/-- The object set `X_θ` is paracompact (a subspace of the metrizable object space). -/
instance paracompactSpace_faceObj (θ : Set X.OrbitSpace) : ParacompactSpace (X.faceObj θ) :=
  X.PObj.paracompactSpace_subtype _

/-- **The face `X_θ` as an ep-groupoid** (Proposition 11.1.6): the full subcategory on `X_θ`
with the induced M-polyfold structures (Proposition 7.1.22, `subEpGroupoid`). -/
def faceEpGroupoid (hX : X.IsEpFaceStructured) (hθ : X.IsOrbitFace θ) :
    EpGroupoid (X.faceObj θ) (X.morOn (X.faceObj θ)) :=
  subEpGroupoid (isEpSubgroupoid_faceObj hX hθ)

/-- Near each point the object M-polyfold of `X_θ` is sc-diffeomorphic to a face of the object
M-polyfold of `X` with its induced structure. -/
theorem exists_isScDiffeoOn_face (hX : X.IsEpFaceStructured) (hθ : X.IsOrbitFace θ)
    (x : X.faceObj θ) :
    ∃ (F : Set Obj) (hF : X.PObj.IsFace F),
      letI : ParacompactSpace F :=
        MPolyfold.paracompactSpace_of_isClosed (MPolyfold.IsFace.isClosed X.PObj hF)
      ∃ (f : X.faceObj θ → F) (g : F → X.faceObj θ) (U : Set (X.faceObj θ)) (V : Set F),
        x ∈ U ∧ (faceEpGroupoid hX hθ).PObj.IsScDiffeoOn
          (MPolyfold.subPolyfold (MPolyfold.theorem_2_5_17_isSubMPolyfold_face X.PObj hX.1
            hX.isWeaklyFaceStructured.2 hF)) f g U V ∧ ∀ y ∈ U, (f y : Obj) = y := by
  obtain ⟨F, hF, hxF, -, U, hU, hxU, hFU⟩ := hX.exists_nhds_eq_face hθ x.2
  have : ParacompactSpace F :=
    MPolyfold.paracompactSpace_of_isClosed (MPolyfold.IsFace.isClosed X.PObj hF)
  have hsubF :=
    MPolyfold.theorem_2_5_17_isSubMPolyfold_face X.PObj hX.1 hX.isWeaklyFaceStructured.2 hF
  have hFU' : X.faceObj θ ∩ U = F ∩ U := hFU
  have hAF : (x : Obj) ∈ U → (x : Obj) ∈ F := fun h => (hFU'.subset ⟨x.2, h⟩).1
  refine ⟨F, hF, MPolyfold.subIncl ⟨x, hAF hxU⟩, MPolyfold.subIncl x, Subtype.val ⁻¹' U,
    Subtype.val ⁻¹' U, hxU,
    MPolyfold.isScDiffeoOn_subPolyfold_of_inter_eq (isSubMPolyfold_faceObj hX hθ) hsubF hU hFU'
      x ⟨x, hAF hxU⟩, fun y hy => ?_⟩
  exact MPolyfold.subIncl_val _ (hFU'.subset ⟨y.2, hy⟩).1

/-- **Proposition 11.1.6**: the induced structure on the object set `X_θ` is tame. -/
theorem isTame_faceEpGroupoid (hX : X.IsEpFaceStructured) (hθ : X.IsOrbitFace θ) :
    (faceEpGroupoid hX hθ).IsTame := by
  refine MPolyfold.isTame_of_forall_exists_chart _ fun x => ?_
  obtain ⟨F, hF, f, g, U, V, hxU, hd, -⟩ := exists_isScDiffeoOn_face hX hθ x
  have : ParacompactSpace F :=
    MPolyfold.paracompactSpace_of_isClosed (MPolyfold.IsFace.isClosed X.PObj hF)
  exact hd.exists_tame_chart
    (MPolyfold.theorem_2_5_17_isTame_face X.PObj hX.1 hX.isWeaklyFaceStructured.2 hF).1 hxU

/-- **Proposition 11.1.6**, the morphism set: the induced structure on the morphisms of `X_θ`
is tame (its source map is a local sc-diffeomorphism onto the tame object M-polyfold). -/
theorem isTame_faceEpGroupoid_mor (hX : X.IsEpFaceStructured) (hθ : X.IsOrbitFace θ) :
    (faceEpGroupoid hX hθ).PMor.IsTame :=
  (faceEpGroupoid hX hθ).isTame_PMor (isTame_faceEpGroupoid hX hθ)

/-- The degeneracy index of the face: `d_X(x) = d_{X_θ}(x) + 1` (Theorem 2.5.17 for the face of
the object M-polyfold through `x`). -/
theorem degIndex_faceEpGroupoid (hX : X.IsEpFaceStructured) (hθ : X.IsOrbitFace θ)
    (x : X.faceObj θ) :
    X.PObj.degIndex x = (faceEpGroupoid hX hθ).PObj.degIndex x + 1 := by
  obtain ⟨F, hF, f, g, U, V, hxU, hd, hf⟩ := exists_isScDiffeoOn_face hX hθ x
  have : ParacompactSpace F :=
    MPolyfold.paracompactSpace_of_isClosed (MPolyfold.IsFace.isClosed X.PObj hF)
  rw [proposition_2_4_4 hd hxU]
  have h :=
    (MPolyfold.theorem_2_5_17_isTame_face X.PObj hX.1 hX.isWeaklyFaceStructured.2 hF).2 (f x)
  rw [hf x hxU] at h
  exact h

/-- **2021 Proposition 11.1.6, p. 524 (2017: Proposition 11.2, p. 378)**, the first part: for a
face structured tame ep-groupoid `X` and a face `X_θ` (`θ` a face of `|X|`), the object set
`X_θ` is a closed saturated sub-M-polyfold of `X` with tame induced structure, the morphism set
`{φ | s(φ), t(φ) ∈ X_θ}` is a sub-M-polyfold with tame induced structure, and the full
subcategory with these structures is an ep-groupoid (`faceEpGroupoid`, the structure maps the
restrictions of those of `X`); moreover `d_X = d_{X_θ} + 1` on `X_θ`. -/
theorem proposition_11_1_6_faces (hX : X.IsEpFaceStructured) (hθ : X.IsOrbitFace θ) :
    X.PObj.IsSubMPolyfold (X.faceObj θ) ∧ IsClosed (X.faceObj θ) ∧
      X.IsSaturated (X.faceObj θ) ∧ (faceEpGroupoid hX hθ).IsTame ∧
      X.PMor.IsSubMPolyfold (X.morOn (X.faceObj θ)) ∧ (faceEpGroupoid hX hθ).PMor.IsTame ∧
      (faceEpGroupoid hX hθ).toGroupoidStr = X.fullSub (X.faceObj θ) ∧
      ∀ x : X.faceObj θ, X.PObj.degIndex x = (faceEpGroupoid hX hθ).PObj.degIndex x + 1 :=
  ⟨isSubMPolyfold_faceObj hX hθ, isClosed_faceObj hθ, isSaturated_faceObj θ,
    isTame_faceEpGroupoid hX hθ, X.isSubMPolyfold_morOn (isEpSubgroupoid_faceObj hX hθ),
    isTame_faceEpGroupoid_mor hX hθ, rfl, degIndex_faceEpGroupoid hX hθ⟩

end EpGroupoid

end Polyfold
