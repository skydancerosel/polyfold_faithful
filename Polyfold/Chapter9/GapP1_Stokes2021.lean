import Polyfold.Chapter4.GapP1_StokesFaceCharts
import Polyfold.Chapter4.GapP1_StokesFaceIntegral
import Polyfold.Chapter9.MathlibFormsBridge2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.4,
**Theorem 4.4.7** (Stokes, p. 199; preprint Theorem 4.28), with the sum over the faces
(gap G.40).

# Stokes' theorem with the sum over the faces

`Q` is an M-polyfold on `Z` with a corner structure of dimension `n + 1` (2021 Definition 4.1.1),
face-structured (Definition 2.5.10; the reading of "whose boundary `∂N` [is] a union of smooth
faces `F`").  Each face `F` is a manifold modelled on `[0,∞)ⁿ` (`faceChartedSpace`,
`hasCornerStructureOfDim_face`), and the inclusion `F → Z` reads in the corner coordinates as a
coordinate face embedding (`FaceData.pair`).

* `goodRegion`: around every point `x₀` the open set of the points signed like `x₀`, close to
  `x₀` (2021 Proposition 2.7.5 (3), `exists_nbhd_faces_mem`) and in the face charts at `x₀` of the
  faces through `x₀`, is a good region (`GoodRegion`): the faces through `x₀` are distinct
  coordinate faces there since every face-structured point of degeneracy index `1` lies on exactly
  one face.
* `faceOrientation`: the induced orientation of each face (`inducedOrientation`).
* **`theorem_4_4_7_hyp`**: for a compact `S ⊆ X` as above, a continuous tangent orientation `o`
  of `S` and `ω ∈ Ωⁿ_∞(X)`, `∫_S (dω)|_S = ∑_F ∫_F ω|_F`, the sum over the (finitely many) faces
  of `S`, each with the induced orientation.
-/

open Set Filter Topology Manifold Module

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- Mathlib's model with corners `[0,∞)ⁿ ⊆ ℝⁿ`. -/
local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

namespace MPolyfold

universe u

open ManifoldForm

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {Q : MPolyfold Z}
  {n : ℕ}

/-! ### Points of degeneracy index `1` -/

/-- A face is paracompact (it is closed). -/
theorem paracompactSpace_face {F : Set Z} (hF : Q.IsFace F) : ParacompactSpace F :=
  paracompactSpace_of_isClosed (IsFace.isClosed Q hF)

/-- **A point of degeneracy index `1` of a face-structured `Q` lies on exactly one face.** -/
theorem exists_face_of_degIndex_eq_one (hfs : Q.IsFaceStructured) {y : Z}
    (hy : Q.degIndex y = 1) : ∃ F, Q.IsFace F ∧ y ∈ F := by
  have h := hfs y
  rw [hy, Nat.cast_one, Set.encard_eq_one] at h
  obtain ⟨F, hF⟩ := h
  have : F ∈ {F | Q.IsFace F ∧ y ∈ F} := hF ▸ mem_singleton F
  exact ⟨F, this⟩

theorem face_eq_of_degIndex_eq_one (hfs : Q.IsFaceStructured) {y : Z} (hy : Q.degIndex y = 1)
    {F F' : Set Z} (hF : Q.IsFace F) (hF' : Q.IsFace F') (hyF : y ∈ F) (hyF' : y ∈ F') :
    F = F' := by
  have h := hfs y
  rw [hy, Nat.cast_one, Set.encard_eq_one] at h
  obtain ⟨G, hG⟩ := h
  have h1 : F ∈ {F | Q.IsFace F ∧ y ∈ F} := ⟨hF, hyF⟩
  have h2 : F' ∈ {F | Q.IsFace F ∧ y ∈ F} := ⟨hF', hyF'⟩
  rw [hG] at h1 h2
  exact h1.trans h2.symm

/-- **Near a point with `yᵢ = 0` there are points whose only vanishing coordinate is `yᵢ`.** -/
theorem CornerCoords.exists_coord_one_zero {m : ℕ} (κ : CornerCoords Q m) {G : Set Z}
    (hG : IsOpen G) {x₀ : Z} (hx₀ : x₀ ∈ G) (hx₀s : x₀ ∈ κ.s) {i : Fin m}
    (hi : κ.coord x₀ i = 0) :
    ∃ y ∈ G, y ∈ κ.s ∧ κ.coord y i = 0 ∧ ∀ l ≠ i, 0 < κ.coord y l := by
  set e := κ.toQuadrantChart
  have hz₀ : e.extend (𝓠 m) x₀ = WithLp.toLp 2 (κ.coord x₀) := κ.extend_eq_toLp_coord hx₀s
  set v : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 fun l => if l = i then 0 else 1
  set f : ℝ → EuclideanSpace ℝ (Fin m) := fun t => e.extend (𝓠 m) x₀ + t • v with hf_def
  have hT : (e.extend (𝓠 m)).symm ⁻¹' G ∩ (e.extend (𝓠 m)).target ∈
      𝓝[range (𝓠 m)] (e.extend (𝓠 m) x₀) :=
    inter_mem (nhdsWithin_le_nhds (e.extend_preimage_mem_nhds hx₀s (hG.mem_nhds hx₀)))
      (e.extend_target_mem_nhdsWithin hx₀s)
  have hf : Tendsto f (𝓝[>] 0) (𝓝[range (𝓠 m)] (e.extend (𝓠 m) x₀)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
      have h0 : f 0 = e.extend (𝓠 m) x₀ := by simp [hf_def]
      exact (h0 ▸ hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      rw [range_modelWithCornersEuclideanQuadrant]
      intro l _
      have hl := κ.coord_nonneg hx₀s l
      simp only [hf_def, v, hz₀, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      split_ifs <;> nlinarith
  obtain ⟨t, htT, ht⟩ := ((hf.eventually hT).and self_mem_nhdsWithin).exists
  have hys : (e.extend (𝓠 m)).symm (f t) ∈ κ.s := by
    rw [← κ.toQuadrantChart_source, ← e.extend_source (I := 𝓠 m)]
    exact (e.extend _).map_target htT.2
  have hye : WithLp.toLp 2 (κ.coord ((e.extend (𝓠 m)).symm (f t))) = f t := by
    rw [← κ.extend_eq_toLp_coord hys]; exact (e.extend _).right_inv htT.2
  obtain ⟨y, hyG, hys, hye⟩ : ∃ y ∈ G, y ∈ κ.s ∧ WithLp.toLp 2 (κ.coord y) = f t :=
    ⟨_, htT.1, hys, hye⟩
  have hft : ∀ l, f t l = κ.coord x₀ l + t * (if l = i then 0 else 1) := fun l => by
    simp only [hf_def, v, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [hz₀]
  refine ⟨y, hyG, hys, ?_, fun l hl => ?_⟩
  · have h := congrArg (fun w : EuclideanSpace ℝ (Fin m) => w i) hye
    simp only [hft, ↓reduceIte, mul_zero, add_zero, hi] at h
    exact h
  · have h := congrArg (fun w : EuclideanSpace ℝ (Fin m) => w l) hye
    simp only [hft, if_neg hl, mul_one] at h
    change κ.coord y l = _ at h
    rw [h]
    linarith [κ.coord_nonneg hx₀s l]

/-! ### The faces as manifolds -/

section FaceManifold

variable (hcs : Q.HasCornerStructureOfDim (n + 1)) (hfs : Q.IsFaceStructured)

/-- **The face `F` as a manifold modelled on `[0,∞)ⁿ`**: the charted space of its corner
structure of dimension `n` (`hasCornerStructureOfDim_face`). -/
@[instance_reducible]
def faceChartedSpace {F : Set Z} (hF : Q.IsFace F) : ChartedSpace (EuclideanQuadrant n) F :=
  haveI := paracompactSpace_face hF
  (subPolyfold (theorem_2_5_17_isSubMPolyfold_face Q hcs.isTame hfs hF)).cornerChartedSpace
    (hasCornerStructureOfDim_face hcs hfs hF)

theorem isManifold_faceChartedSpace {F : Set Z} (hF : Q.IsFace F) :
    letI := faceChartedSpace hcs hfs hF
    IsManifold (𝓠 n) ∞ F :=
  haveI := paracompactSpace_face hF
  isManifold_of_eq (hasCornerStructureOfDim_face hcs hfs hF)
    (inst := faceChartedSpace hcs hfs hF) rfl

variable [inst : ChartedSpace (EuclideanQuadrant (n + 1)) Z]
  (hch : inst = Q.cornerChartedSpace hcs)
include hch

/-- **The face chart pair of face data**: the corner coordinates `removeNth i ∘ κ.coord` of the
face `F` (`FaceData.coords`) and `κ`, in which the inclusion `F → Z` is the face embedding
`insertNth i 0`. -/
def FaceData.pair {κ : CornerCoords Q (n + 1)} {F : Set Z} (hF : Q.IsFace F)
    (D : FaceData κ F) (c : F) :
    letI := faceChartedSpace hcs hfs hF
    FaceChartPair n (Subtype.val : F → Z) :=
  letI := faceChartedSpace hcs hfs hF
  haveI := paracompactSpace_face hF
  { eN := (D.coords c (theorem_2_5_17_isSubMPolyfold_face Q hcs.isTame hfs hF)).toQuadrantChart
    e := κ.toQuadrantChart
    i := D.i
    mem_N := mem_maximalAtlas_of_eq (hasCornerStructureOfDim_face hcs hfs hF)
      (inst := faceChartedSpace hcs hfs hF) rfl _
    mem_M := mem_maximalAtlas_of_eq hcs hch κ
    mapsTo := fun _ hp => D.V₁_subset hp
    extend_eq := fun p hp => by
      rw [κ.extend_eq_toLp_coord (D.V₁_subset hp), CornerCoords.extend_eq_toLp_coord _ hp,
        FaceData.coords_coord, removeL_apply]
      exact (faceEmbedding_removeNth (x := WithLp.toLp 2 (κ.coord p))
        (D.coord_eq_zero p.2 hp)).symm }

theorem FaceData.pair_e {κ : CornerCoords Q (n + 1)} {F : Set Z} (hF : Q.IsFace F)
    (D : FaceData κ F) (c : F) :
    letI := faceChartedSpace hcs hfs hF
    (D.pair hcs hfs hch hF c).e = κ.toQuadrantChart := rfl

theorem FaceData.pair_i {κ : CornerCoords Q (n + 1)} {F : Set Z} (hF : Q.IsFace F)
    (D : FaceData κ F) (c : F) :
    letI := faceChartedSpace hcs hfs hF
    (D.pair hcs hfs hch hF c).i = D.i := rfl

theorem FaceData.mem_pair_source {κ : CornerCoords Q (n + 1)} {F : Set Z} (hF : Q.IsFace F)
    (D : FaceData κ F) (c : F) {p : F} (hp : (p : Z) ∈ D.V₁) :
    letI := faceChartedSpace hcs hfs hF
    p ∈ (D.pair hcs hfs hch hF c).eN.source := hp

end FaceManifold

/-! ### Good regions -/

section Good

variable (Q) in
/-- The faces of `Q`, the index type of the sum `∑_F` of 2021 Theorem 4.4.7. -/
abbrev Faces : Type u := {F : Set Z // Q.IsFace F}

variable (hcs : Q.HasCornerStructureOfDim (n + 1)) (hfs : Q.IsFaceStructured)

include hcs in
theorem finite_facesAt (x₀ : Z) : {a : Faces Q | x₀ ∈ a.1}.Finite :=
  ((finite_setOf_isFace_mem hcs.isTame x₀).preimage Subtype.val_injective.injOn).subset
    fun a h => ⟨a.2, h⟩

/-- The faces through `x₀`. -/
def facesAt (x₀ : Z) : Finset (Faces Q) := (finite_facesAt hcs x₀).toFinset

theorem mem_facesAt {x₀ : Z} {a : Faces Q} : a ∈ facesAt hcs x₀ ↔ x₀ ∈ a.1 :=
  Set.Finite.mem_toFinset _

include hfs in
theorem exists_faceDataAt (x₀ : Z) (a : Faces Q) (h : x₀ ∈ a.1) :
    ∃ D : FaceData (hcs.coords x₀) a.1, (hcs.coords x₀).coord x₀ D.i = 0 ∧
      (hcs.coords x₀).coord x₀ ∈ D.B ∧ D.B ⊆ univ :=
  (hcs.coords x₀).exists_faceData hfs a.2 h (hcs.mem_coords x₀) isOpen_univ (mem_univ _)

/-- The face data at `x₀` of a face through `x₀`. -/
def faceDataAt (x₀ : Z) (a : Faces Q) (h : x₀ ∈ a.1) : FaceData (hcs.coords x₀) a.1 :=
  (exists_faceDataAt hcs hfs x₀ a h).choose

theorem faceDataAt_coord (x₀ : Z) (a : Faces Q) (h : x₀ ∈ a.1) :
    (hcs.coords x₀).coord x₀ (faceDataAt hcs hfs x₀ a h).i = 0 :=
  (exists_faceDataAt hcs hfs x₀ a h).choose_spec.1

theorem mem_faceDataAt_V₁ (x₀ : Z) (a : Faces Q) (h : x₀ ∈ a.1) :
    x₀ ∈ (faceDataAt hcs hfs x₀ a h).V₁ :=
  ⟨hcs.mem_coords x₀, (exists_faceDataAt hcs hfs x₀ a h).choose_spec.2.1⟩

open Classical in
/-- The domain of the face chart at `x₀` of a face through `x₀` (`univ` for the other faces). -/
def V₁At (x₀ : Z) (a : Faces Q) : Set Z :=
  if h : x₀ ∈ a.1 then (faceDataAt hcs hfs x₀ a h).V₁ else univ

theorem isOpen_V₁At (x₀ : Z) (a : Faces Q) : IsOpen (V₁At hcs hfs x₀ a) := by
  unfold V₁At
  split_ifs
  · exact FaceData.isOpen_V₁ _
  · exact isOpen_univ

theorem mem_V₁At_iff {x₀ y : Z} {a : Faces Q} (h : x₀ ∈ a.1) :
    y ∈ V₁At hcs hfs x₀ a ↔ y ∈ (faceDataAt hcs hfs x₀ a h).V₁ := by
  rw [V₁At, dif_pos h]

include hcs in
theorem exists_nbhdFaces (x₀ : Z) :
    ∃ U, IsOpen U ∧ x₀ ∈ U ∧ U ⊆ univ ∧ ∀ θ, TameBoundary.IsFaceIn Q.degIndex univ θ →
      ∀ y ∈ U, y ∈ θ → x₀ ∈ θ :=
  TameBoundary.exists_nbhd_faces_mem (Q.isCornerIndex_degIndex hcs.isTame) isOpen_univ
    (mem_univ x₀)

/-- A neighbourhood of `x₀` meeting only the faces through `x₀` (2021 Proposition 2.7.5 (3)). -/
def nbhdFaces (x₀ : Z) : Set Z := (exists_nbhdFaces hcs x₀).choose

variable [inst : ChartedSpace (EuclideanQuadrant (n + 1)) Z]
  (o : TangentOrientation (𝓠 (n + 1)) Z (n + 1))

/-- The points of the piece of `hcs.coords x₀` where `o` reads as at `x₀`. -/
def signRegion (x₀ : Z) : Set Z :=
  {y | y ∈ (hcs.coords x₀).s ∧ orientationIn (hcs.coords x₀).toQuadrantChart y (o y) =
    orientationIn (hcs.coords x₀).toQuadrantChart x₀ (o x₀)}

/-- **The good region at `x₀`.** -/
def goodSet (x₀ : Z) : Set Z :=
  signRegion hcs o x₀ ∩ nbhdFaces hcs x₀ ∩ ⋂ a ∈ {a : Faces Q | x₀ ∈ a.1}, V₁At hcs hfs x₀ a

theorem mem_goodSet (x₀ : Z) : x₀ ∈ goodSet hcs hfs o x₀ :=
  ⟨⟨⟨hcs.mem_coords x₀, rfl⟩, (exists_nbhdFaces hcs x₀).choose_spec.2.1⟩,
    mem_iInter₂.2 fun a h => (mem_V₁At_iff hcs hfs h).2 (mem_faceDataAt_V₁ hcs hfs x₀ a h)⟩

variable (hch : inst = Q.cornerChartedSpace hcs)
include hch

theorem isOpen_goodSet (ho : o.IsContinuous (𝓠 (n + 1)) ∞) (x₀ : Z) :
    IsOpen (goodSet hcs hfs o x₀) := by
  have hR : IsOpen (signRegion hcs o x₀) := by
    refine isOpen_iff_mem_nhds.2 fun y hy => ?_
    filter_upwards [(hcs.coords x₀).isOpen_s.mem_nhds hy.1,
      ho _ (mem_maximalAtlas_of_eq hcs hch _) y hy.1] with z hz hz'
    exact ⟨hz, hz'.trans hy.2⟩
  exact (hR.inter (exists_nbhdFaces hcs x₀).choose_spec.1).inter
    ((finite_facesAt hcs x₀).isOpen_biInter fun a _ => isOpen_V₁At hcs hfs x₀ a)

open Classical in
/-- **Every point has a good region** (`GoodRegion`): the region `goodSet x₀` in the chart
`hcs.coords x₀` (the chart `chartAt x₀`), with the face chart pairs of the faces through `x₀`. -/
def goodRegion (ho : o.IsContinuous (𝓠 (n + 1)) ∞) (x₀ : Z) :
    letI : ∀ a : Faces Q, ChartedSpace (EuclideanQuadrant n) a.1 :=
      fun a => faceChartedSpace hcs hfs a.2
    GoodRegion o (fun (a : Faces Q) (p : a.1) => (p : Z)) (hcs.coords x₀).toQuadrantChart
      (goodSet hcs hfs o x₀) :=
  letI : ∀ a : Faces Q, ChartedSpace (EuclideanQuadrant n) a.1 :=
    fun a => faceChartedSpace hcs hfs a.2
  { sign := decide (orientationIn (hcs.coords x₀).toQuadrantChart x₀ (o x₀) =
      stdOrientation (n + 1))
    orientationIn_eq := fun _ hy => hy.1.1.2.trans (eq_signedOr_decide _)
    subset_source := fun _ hy => hy.1.1.1
    faces := facesAt hcs x₀
    pair := fun a h => (faceDataAt hcs hfs x₀ a ((mem_facesAt hcs).1 h)).pair hcs hfs hch a.2
      ⟨x₀, (mem_facesAt hcs).1 h⟩
    pair_e := fun _ _ => rfl
    src := fun a h p hp => FaceData.mem_pair_source hcs hfs hch a.2 _ _
      ((mem_V₁At_iff hcs hfs ((mem_facesAt hcs).1 h)).1
        (mem_iInter₂.1 hp.2 a ((mem_facesAt hcs).1 h)))
    miss := fun a h p hp => h ((mem_facesAt hcs).2
      ((exists_nbhdFaces hcs x₀).choose_spec.2.2.2 a.1 ((Q.isFaceIn_univ_iff).2 a.2) p hp.1.2 p.2))
    inj := fun a h a' h' hi => by
      have ha := (mem_facesAt hcs).1 h
      have ha' := (mem_facesAt hcs).1 h'
      set κ := hcs.coords x₀
      have hi' : (faceDataAt hcs hfs x₀ a ha).i = (faceDataAt hcs hfs x₀ a' ha').i := hi
      obtain ⟨y, hyG, hys, hyi, hyl⟩ := κ.exists_coord_one_zero (isOpen_goodSet hcs hfs o hch ho x₀)
        (mem_goodSet hcs hfs o x₀) (hcs.mem_coords x₀) (faceDataAt_coord hcs hfs x₀ a ha)
      have hyV : ∀ b (hb : x₀ ∈ b.1), y ∈ (faceDataAt hcs hfs x₀ b hb).V₁ := fun b hb =>
        (mem_V₁At_iff hcs hfs hb).1 (mem_iInter₂.1 hyG.2 b hb)
      have hya : y ∈ a.1 := (faceDataAt hcs hfs x₀ a ha).mem_of_coord_eq_zero (hyV a ha) hyi
      have hya' : y ∈ a'.1 :=
        (faceDataAt hcs hfs x₀ a' ha').mem_of_coord_eq_zero (hyV a' ha') (hi' ▸ hyi)
      have hd := κ.degIndex_eq_one hys hyi fun l hl => (hyl l hl).ne'
      exact Subtype.ext (face_eq_of_degIndex_eq_one hfs hd a.2 a'.2 hya hya')
    cover := fun x hx i hi hl => by
      set κ := hcs.coords x₀
      have hxs : x ∈ κ.s := hx.1.1.1
      have he := κ.extend_eq_toLp_coord hxs
      rw [he] at hi hl
      obtain ⟨F, hF, hxF⟩ := exists_face_of_degIndex_eq_one hfs
        (κ.degIndex_eq_one hxs hi fun l hl' => (hl l hl').ne')
      exact ⟨⟨F, hF⟩, ⟨x, hxF⟩, rfl⟩ }

/-- Every point of a face lies in a face chart pair. -/
theorem exists_faceChartPair_face (a : Faces Q) (p : a.1) :
    letI := faceChartedSpace hcs hfs a.2
    ∃ P : FaceChartPair n (Subtype.val : a.1 → Z), p ∈ P.eN.source :=
  letI := faceChartedSpace hcs hfs a.2
  ⟨(faceDataAt hcs hfs p.1 a p.2).pair hcs hfs hch a.2 p,
    FaceData.mem_pair_source hcs hfs hch a.2 _ _ (mem_faceDataAt_V₁ hcs hfs p.1 a p.2)⟩

/-- **The induced orientation of a face** (2021 Theorem 4.4.7, "equipped with the induced
orientation"; `IsInducedOrientation`, outward vector first). -/
def faceOrientation (a : Faces Q) :
    letI := faceChartedSpace hcs hfs a.2
    TangentOrientation (𝓠 n) a.1 n :=
  letI := faceChartedSpace hcs hfs a.2
  haveI := isManifold_faceChartedSpace hcs hfs a.2
  inducedOrientation o (exists_faceChartPair_face hcs hfs hch a)

theorem isInducedOrientation_faceOrientation (a : Faces Q) :
    letI := faceChartedSpace hcs hfs a.2
    IsInducedOrientation (Subtype.val : a.1 → Z) o (faceOrientation hcs hfs o hch a) :=
  letI := faceChartedSpace hcs hfs a.2
  haveI := isManifold_faceChartedSpace hcs hfs a.2
  haveI := isManifold_of_eq hcs hch
  isInducedOrientation_inducedOrientation o (exists_faceChartPair_face hcs hfs hch a)

theorem isContinuous_faceOrientation (ho : o.IsContinuous (𝓠 (n + 1)) ∞) (a : Faces Q) :
    letI := faceChartedSpace hcs hfs a.2
    (faceOrientation hcs hfs o hch a).IsContinuous (𝓠 n) ∞ :=
  letI := faceChartedSpace hcs hfs a.2
  haveI := isManifold_faceChartedSpace hcs hfs a.2
  haveI := isManifold_of_eq hcs hch
  isContinuous_inducedOrientation o (exists_faceChartPair_face hcs hfs hch a) ho
    continuous_subtype_val

end Good

/-! ### Theorem 4.4.7 -/

section Theorem447

/-- **The face-structure hypothesis is satisfiable**: without boundary points (`d_Z = 0`, e.g. a
closed manifold) there are no faces and `Z` is face-structured; the quadrants are face-structured
(`isFaceStructured_quadrant`). -/
theorem isFaceStructured_of_forall_degIndex_eq_zero (h : ∀ x, Q.degIndex x = 0) :
    Q.IsFaceStructured := fun x => by
  rw [h x, Nat.cast_zero, Set.encard_eq_zero]
  ext F
  simp only [Set.mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
  rintro ⟨y, hy, -⟩
  rw [h y] at hy
  exact absurd hy zero_ne_one

/-- **A compact `Z` has finitely many faces** (`finite_setOf_isFace`). -/
theorem finite_faces [CompactSpace Z] (hcs : Q.HasCornerStructureOfDim (n + 1)) :
    Finite (Faces Q) :=
  (finite_setOf_isFace hcs.isTame).to_subtype

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {S : Set X} [ParacompactSpace S] [CompactSpace S] {hY : PX.IsSubMPolyfold S}
  {hcs : (subPolyfold hY).HasCornerStructureOfDim (n + 1)}
  (hfs : (subPolyfold hY).IsFaceStructured)
  [inst : ChartedSpace (EuclideanQuadrant (n + 1)) S]
  (hch : inst = (subPolyfold hY).cornerChartedSpace hcs)

/-- **2021 Theorem 4.4.7** (Stokes, p. 199; preprint Theorem 4.28), with the sum over the faces:
let `S ⊆ X` be a compact sub-M-polyfold with a corner structure of dimension `n + 1` (an
`(n+1)`-dimensional compact tame submanifold, `inst` its Mathlib charted space), face-structured
(the reading of "whose boundary `∂N` [is] a union of smooth faces `F`", Definition 2.5.10),
oriented by a continuous tangent orientation `o`, and `ω ∈ Ωⁿ_∞(X)`.  Then
`∫_S (dω)|_S = ∑_F ∫_F ω|_F`, the sum over the finitely many faces `F` of `S`, each a manifold
modelled on `[0,∞)ⁿ` (`faceChartedSpace`) with the induced orientation (`faceOrientation`,
outward vector first), `ω|_F` the restriction of `ω|_S` along `F ↪ S` (`restrictForm`).
The added hypotheses: `S` face-structured, and `ω|_S`, `d` read through
`formsInftyRestrict` (gap G.80). -/
theorem theorem_4_4_7_hyp {o : TangentOrientation (𝓠 (n + 1)) S (n + 1)}
    (ho : o.IsContinuous (𝓠 (n + 1)) ∞) (ω : (BundledMPolyfold.of PX).formsInfty n) :
    haveI := isManifold_of_eq hcs hch
    letI : Fintype (Faces (subPolyfold hY)) := @Fintype.ofFinite _ (finite_faces hcs)
    letI : ∀ a : Faces (subPolyfold hY), ChartedSpace (EuclideanQuadrant n) a.1 :=
      fun a => faceChartedSpace hcs hfs a.2
    ManifoldForm.integral o
        (formsInftyRestrict (n + 1) hcs ((BundledMPolyfold.of PX).formsInftyD n ω)) =
      ∑ a : Faces (subPolyfold hY), ManifoldForm.integral (faceOrientation hcs hfs o hch a)
        (restrictForm (Subtype.val : a.1 → S) (formsInftyRestrict n hcs ω)) := by
  have := isManifold_of_eq hcs hch
  let _ : Fintype (Faces (subPolyfold hY)) := @Fintype.ofFinite _ (finite_faces hcs)
  let _ : ∀ a : Faces (subPolyfold hY), ChartedSpace (EuclideanQuadrant n) a.1 :=
    fun a => faceChartedSpace hcs hfs a.2
  have : ∀ a : Faces (subPolyfold hY), IsManifold (𝓠 n) ∞ a.1 :=
    fun a => isManifold_faceChartedSpace hcs hfs a.2
  have : ∀ a : Faces (subPolyfold hY), CompactSpace a.1 :=
    fun a => isCompact_iff_compactSpace.1 (IsFace.isClosed _ a.2).isCompact
  have hω : ManifoldForm.ContMDiffForm (𝓠 (n + 1)) 1 (formsInftyRestrict n hcs ω) :=
    (contMDiffForm_formsInftyRestrict hch ω).of_le (by exact_mod_cast le_top)
  rw [stokes_formsInftyRestrict hch ho ω]
  subst hch
  let _ := (subPolyfold hY).cornerChartedSpace hcs
  exact (sum_integral_restrictForm_eq_boundaryIntegral o
    (fun (a : Faces (subPolyfold hY)) (p : a.1) => (p : S)) ho (fun _ => continuous_subtype_val)
    (fun a => isInducedOrientation_faceOrientation hcs hfs o rfl a)
    (fun a => isContinuous_faceOrientation hcs hfs o rfl ho a) (goodSet hcs hfs o)
    (isOpen_goodSet hcs hfs o rfl ho) (mem_goodSet hcs hfs o) (goodRegion hcs hfs o rfl ho) hω
    isClosed_closure.isCompact).symm

end Theorem447

end MPolyfold

end Polyfold
