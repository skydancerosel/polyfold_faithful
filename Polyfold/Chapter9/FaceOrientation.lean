import Polyfold.Chapter9.BoundaryOrientation
import Polyfold.Chapter9.StokesFaceSum

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
§9.3, Definition 9.3.8, p. 427 (2017: Definition 9.9), Figure 9.1, and Part I, Theorem 4.4.7,
p. 199 ("equipped with the induced orientation").

# The two boundary orientations agree

A tame `(m+1)`-dimensional sheet `M` of an M-polyfold `X`, face-structured and oriented by an
orientation `o` of Definition 9.3.3, carries two boundary orientations:

* Part II's `o_{∂M}` (Definition 9.3.8): an orientation, in the sense of Definition 9.3.3, of the
  `m`-dimensional submanifold `{d_M = 1}` of `X`, with frames in `TX`
  (`SubmanifoldOrientation.stratumOrientation`);
* Part I's induced orientation of each closed face `F` of the manifold with corners `M`
  (`faceOrientation`, a Mathlib `TangentOrientation` of the face manifold `F`, read in face
  chart pairs with the rule "outward normal first", `IsInducedOrientation`), applied to the
  tangent orientation `bridgeOrientation o` of `M`.

**`faceOrientation_eq_iff_mem_stratumOrientation`**: at every point `p` of a face with
`d_M(p) = 1` they agree: in a face chart pair `(e_F, κ, i)` (`κ` corner coordinates of `M`, the
face `{yᵢ = 0}`), a basis `b` of `ℝᵐ` is positive for the face orientation iff the frame
`Tι(ιᵢ b₁), …, Tι(ιᵢ b_m)` of `T_p∂M ⊆ T_pX` is positive for `o_{∂M}` (`ιᵢ = faceEmbedding i`,
`Tι` the tangent map of `M ↪ X` in the coordinates `κ`, `incFrame`).
`faceOrientation_eq_iff_mem_stratumOrientation_pair`: the same in the face chart pairs of the
face data (`FaceData.pair`), the charts of Part I's face manifolds.

**`figure_9_1_existsUnique_faceOrientation`** (Figure 9.1 and the paragraph before it: the
orientation of the interior of a boundary face extends to the closed face): on a closed face `F`
there is exactly one continuous tangent orientation agreeing with `o_{∂M}` at the points of `F`
with `d_M = 1` (`IsBoundaryOrientedAt`), namely `faceOrientation (bridgeOrientation o)`.  The
inputs: those points are dense in `F` (`dense_faceStratum`), and two continuous tangent
orientations agreeing on a dense set are equal (`TangentOrientation.eq_of_eqOn_dense`).

The linear algebra: `det(−eᵢ, ιᵢ v₁, …, ιᵢ v_m) = faceSign i · det v`
(`det_cons_neg_stdFrame_faceEmbedding`), and the basis `(−eᵢ, ιᵢ b)` of `ℝᵐ⁺¹`
(`consFaceBasis`) has orientation `ρ` iff `b` has the orientation Part I's rule assigns to `ρ`
(`orientation_consFaceBasis_eq_iff`).
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Module Manifold

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

universe u

/-! ### Linear algebra: outward normal first -/

section LinAlg

variable {m : ℕ}

/-- **`det(−eᵢ, ιᵢ v₁, …, ιᵢ v_m) = faceSign i · det v`**, the determinants with respect to the
standard bases (`ιᵢ = faceEmbedding i`). -/
theorem det_cons_neg_stdFrame_faceEmbedding (i : Fin (m + 1))
    (v : Fin m → EuclideanSpace ℝ (Fin m)) :
    (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis.det
        (Fin.cons (-stdFrame (m + 1) i) (faceEmbedding i ∘ v)) =
      faceSign i * (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.det v := by
  set b₁ := (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis
  set b₀ := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
  set f : EuclideanSpace ℝ (Fin m) [⋀^Fin m]→ₗ[ℝ] ℝ :=
    (b₁.det.curryLeft (-stdFrame (m + 1) i)).compLinearMap
      (faceEmbedding i : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))
  have hf : ∀ w, f w = b₁.det (Fin.cons (-stdFrame (m + 1) i) (faceEmbedding i ∘ w)) :=
    fun w => rfl
  have h := congrArg (fun g : EuclideanSpace ℝ (Fin m) [⋀^Fin m]→ₗ[ℝ] ℝ => g v)
    (f.eq_smul_basis_det b₀)
  simp only [AlternatingMap.smul_apply, smul_eq_mul] at h
  rw [← hf, h, hf, coe_basisFun_toBasis, det_cons_neg_stdFrame_faceFrame]

theorem faceSign_ne_zero (i : Fin (m + 1)) : faceSign i ≠ 0 :=
  pow_ne_zero _ (by norm_num)

theorem isUnit_det_cons_faceEmbedding (i : Fin (m + 1))
    (b : Basis (Fin m) ℝ (EuclideanSpace ℝ (Fin m))) :
    IsUnit ((EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis.det
      (Fin.cons (-stdFrame (m + 1) i) (faceEmbedding i ∘ b))) := by
  rw [det_cons_neg_stdFrame_faceEmbedding]
  exact isUnit_iff_ne_zero.2
    (mul_ne_zero (faceSign_ne_zero i) (Basis.isUnit_det _ b).ne_zero)

/-- **The basis `(−eᵢ, ιᵢ b₁, …, ιᵢ b_m)` of `ℝᵐ⁺¹`**: the outward normal of the face
`{xᵢ = 0}` of the quadrant followed by the image of a basis of the face. -/
def consFaceBasis (i : Fin (m + 1)) (b : Basis (Fin m) ℝ (EuclideanSpace ℝ (Fin m))) :
    Basis (Fin (m + 1)) ℝ (EuclideanSpace ℝ (Fin (m + 1))) :=
  Basis.mk (((EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis.is_basis_iff_det).2
      (isUnit_det_cons_faceEmbedding i b)).1
    (((EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis.is_basis_iff_det).2
      (isUnit_det_cons_faceEmbedding i b)).2.ge

theorem coe_consFaceBasis (i : Fin (m + 1)) (b : Basis (Fin m) ℝ (EuclideanSpace ℝ (Fin m))) :
    ⇑(consFaceBasis i b) = Fin.cons (-stdFrame (m + 1) i) (faceEmbedding i ∘ b) :=
  Basis.coe_mk (v := Fin.cons (-stdFrame (m + 1) i) (faceEmbedding i ∘ b)) _ _

open Classical in
/-- An orientation of `ℝᵏ` is `signedOr c` of the standard one iff `c` records whether it is the
standard one. -/
theorem eq_signedOr_std_iff {k : ℕ} (r : Orientation ℝ (EuclideanSpace ℝ (Fin k)) (Fin k))
    (c : Bool) : r = signedOr c (stdOrientation k) ↔ decide (r = stdOrientation k) = c := by
  cases c
  · simp only [signedOr_false, decide_eq_false_iff_not]
    constructor
    · rintro h h'
      exact Module.Ray.ne_neg_self (stdOrientation k) (h'.symm.trans h)
    · intro h
      have := eq_signedOr_decide r
      simp only [h, decide_false, signedOr_false] at this
      exact this
  · simp

theorem orientation_eq_std_iff_det_pos {k : ℕ}
    (b : Basis (Fin k) ℝ (EuclideanSpace ℝ (Fin k))) :
    b.orientation = stdOrientation k ↔ 0 < (EuclideanSpace.basisFun (Fin k) ℝ).toBasis.det b := by
  rw [stdOrientation, eq_comm, Basis.orientation_eq_iff_det_pos]

open Classical in
/-- `(−eᵢ, ιᵢ b)` is positive iff `b` is positive exactly when `faceSign i = 1`. -/
theorem decide_orientation_consFaceBasis (i : Fin (m + 1))
    (b : Basis (Fin m) ℝ (EuclideanSpace ℝ (Fin m))) :
    decide ((consFaceBasis i b).orientation = stdOrientation (m + 1)) =
      (faceBool i == decide (b.orientation = stdOrientation m)) := by
  have h1 := orientation_eq_std_iff_det_pos (consFaceBasis i b)
  rw [coe_consFaceBasis, det_cons_neg_stdFrame_faceEmbedding] at h1
  have h2 := orientation_eq_std_iff_det_pos b
  have hd : (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.det b ≠ 0 :=
    (Basis.isUnit_det _ b).ne_zero
  set d := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.det b
  have hfb : faceBool i = decide (faceSign i = 1) := rfl
  rcases neg_one_pow_eq_or ℝ ((i : ℕ) + 1) with hs | hs
  · have hs' : faceSign i = 1 := hs
    rw [hs', one_mul] at h1
    rw [hfb, hs']
    by_cases hb : 0 < d
    · rw [decide_eq_true (h1.2 hb), decide_eq_true (h2.2 hb)]; simp
    · rw [decide_eq_false (fun h => hb (h1.1 h)), decide_eq_false (fun h => hb (h2.1 h))]; simp
  · have hs' : faceSign i = -1 := hs
    rw [hs', neg_one_mul] at h1
    rw [hfb, hs', decide_eq_false (by norm_num : (-1 : ℝ) ≠ 1)]
    by_cases hb : 0 < d
    · rw [decide_eq_false (fun h => by linarith [h1.1 h]), decide_eq_true (h2.2 hb)]; simp
    · have hneg : 0 < -d := by
        rcases lt_or_gt_of_ne hd with h | h
        · linarith
        · exact absurd h hb
      rw [decide_eq_true (h1.2 hneg), decide_eq_false (fun h => hb (h2.1 h))]; simp

open Classical in
/-- **Outward normal first, in `ℝᵐ⁺¹`**: the basis `(−eᵢ, ιᵢ b)` has the orientation `ρ` iff `b`
has the orientation `orSign (s == faceBool i)` times the standard one, `s` the sign of `ρ` — the
orientation Part I's rule (`IsInducedOrientation`, `FaceChartPair.boundarySign`) assigns to the
face `{xᵢ = 0}` when the quadrant is oriented by `ρ`. -/
theorem orientation_consFaceBasis_eq_iff (i : Fin (m + 1))
    (b : Basis (Fin m) ℝ (EuclideanSpace ℝ (Fin m)))
    (ρ : Orientation ℝ (EuclideanSpace ℝ (Fin (m + 1))) (Fin (m + 1))) :
    (consFaceBasis i b).orientation = ρ ↔
      b.orientation =
        signedOr (decide (ρ = stdOrientation (m + 1)) == faceBool i) (stdOrientation m) := by
  have key : ∀ c : Bool, ((consFaceBasis i b).orientation = signedOr c (stdOrientation (m + 1)) ↔
      b.orientation = signedOr (c == faceBool i) (stdOrientation m)) := fun c => by
    rw [eq_signedOr_std_iff, eq_signedOr_std_iff, decide_orientation_consFaceBasis]
    generalize faceBool i = f
    generalize decide (b.orientation = stdOrientation m) = t
    cases c <;> cases f <;> cases t <;> decide
  have h := key (decide (ρ = stdOrientation (m + 1)))
  rwa [← eq_signedOr_decide ρ] at h

end LinAlg

/-! ### The face orientation and `o_{∂M}` -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {M : Set X} [ParacompactSpace M] {m : ℕ} {hY : P.IsSubMPolyfold M}

/-- At a point with `d = 1` in corner coordinates in which `yᵢ = 0`, the point lies in the face
piece of `i`. -/
theorem CornerCoords.mem_facePiece_of_degIndex_eq_one {Z : Type u} [TopologicalSpace Z]
    [T2Space Z] [ParacompactSpace Z] {Q : MPolyfold Z} {n : ℕ} (κ : CornerCoords Q n) {z : Z}
    (hz : z ∈ κ.s) (hd : Q.degIndex z = 1) {i : Fin n} (hi : κ.coord z i = 0) :
    z ∈ κ.facePiece i := by
  have hcard : (Finset.univ.filter fun j => κ.coord z j = 0).card = 1 := by
    rw [← κ.degIndex_eq_card hz]; exact hd
  obtain ⟨i', hi'⟩ := Finset.card_eq_one.1 hcard
  have hmem : ∀ l, κ.coord z l = 0 → l = i' := fun l hl => by
    have : l ∈ Finset.univ.filter fun j => κ.coord z j = 0 :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hl⟩
    rw [hi'] at this
    exact Finset.mem_singleton.1 this
  refine ⟨hz, fun l hl => ?_, ?_⟩
  · refine lt_of_le_of_ne (κ.coord_nonneg hz l) fun h0 => hl ?_
    rw [hmem l h0.symm, hmem i hi]
  · rw [← hi, Function.update_eq_self]
    exact κ.coord_mem_W hz

variable (hcs : (subPolyfold hY).HasCornerStructureOfDim (m + 1))
  (hfs : (subPolyfold hY).IsFaceStructured)
  [inst : ChartedSpace (EuclideanQuadrant (m + 1)) M]
  (hch : inst = (subPolyfold hY).cornerChartedSpace hcs)

omit inst in
include hcs in
/-- A tame sheet: the induced structure is tame. -/
theorem hasTameInducedStructure_of_hasCornerStructureOfDim :
    P.HasTameInducedStructure M :=
  ⟨hY, hcs.isTame⟩

include hch in
open Classical in
/-- **The two boundary orientations agree** (2021 Definition 9.3.8, p. 427, and Figure 9.1, with
Part I's Theorem 4.4.7, p. 199, "equipped with the induced orientation"): let `M` be a tame,
face-structured `(m+1)`-dimensional submanifold of `X` oriented by `o` (Definition 9.3.3), `F` a
face of `M` with Part I's induced orientation of the tangent orientation `bridgeOrientation o`
(`faceOrientation`), and `p ∈ F` with `d_M(p) = 1`.  In a face chart pair `(e_F, κ, i)` at `p`
(`κ` corner coordinates of `M`, the face `{yᵢ = 0}`), a basis `b` of `ℝᵐ` is positive for the
face orientation iff the frame `Tι(ιᵢ b₁), …, Tι(ιᵢ b_m)` of `T_p∂M ⊆ T_pX` is positive for the
boundary orientation `o_{∂M}` of Definition 9.3.8 (`stratumOrientation`). -/
theorem faceOrientation_eq_iff_mem_stratumOrientation (hM : P.IsSubmanifoldOfDim M (m + 1))
    (o : P.SubmanifoldOrientation M (m + 1)) (a : MPolyfold.Faces (subPolyfold hY))
    (κ : CornerCoords (subPolyfold hY) (m + 1)) :
    letI := faceChartedSpace hcs hfs a.2
    ∀ (Pr : FaceChartPair m (Subtype.val : a.1 → M)), Pr.e = κ.toQuadrantChart →
    ∀ {p : a.1}, p ∈ Pr.eN.source → (subPolyfold hY).degIndex (p : M) = 1 →
    ∀ (hps : (p : M) ∈ κ.s) (b : Basis (Fin m) ℝ (EuclideanSpace ℝ (Fin m))),
    (b.orientation =
        orientationIn Pr.eN p (faceOrientation hcs hfs (bridgeOrientation hcs o) hch a p) ↔
      (fun j => incFrame hcs κ hps (faceEmbedding Pr.i (b j))) ∈
        (o.stratumOrientation hM (hasTameInducedStructure_of_hasCornerStructureOfDim hcs)).frames
          (p : M).1) := by
  intro Pr hPe p hp hd hps b
  let _ := faceChartedSpace hcs hfs a.2
  have hman := isManifold_of_eq hcs hch
  have h1 := isInducedOrientation_faceOrientation hcs hfs (bridgeOrientation hcs o) hch a Pr p hp
  rw [h1]
  have h2 : orientationIn Pr.e (p : M) (bridgeOrientation hcs o (p : M)) = orIn hcs o κ hps := by
    rw [hPe]; exact orientationIn_bridgeOrientation hch (Nat.succ_pos m) hM o κ hps
  have hbs : Pr.boundarySign (bridgeOrientation hcs o) p =
      (decide (orIn hcs o κ hps = stdOrientation (m + 1)) == faceBool Pr.i) := by
    unfold FaceChartPair.boundarySign; rw [h2]
  rw [hbs, ← orientation_consFaceBasis_eq_iff, orientation_eq_orIn_iff (Nat.succ_pos m) hM o κ hps,
    coe_consFaceBasis, SubmanifoldOrientation.stratumOrientation_frames]
  have hi : κ.coord (p : M) Pr.i = 0 := by
    have h := Pr.extend_coord_eq_zero hp
    rw [hPe, κ.extend_eq_toLp_coord hps] at h
    exact h
  have hpiece : (p : M) ∈ κ.facePiece Pr.i := κ.mem_facePiece_of_degIndex_eq_one hps hd hi
  rw [incFrame_mem_boundaryFramesAt_iff hcs hM
    (hasTameInducedStructure_of_hasCornerStructureOfDim hcs)
    o κ hpiece hi (fun j => faceEmbedding Pr.i (b j)) (fun j => by simp [mem_coordHyperplane])]
  have hfun : (fun k => incFrame hcs κ hps
      ((Fin.cons (-stdFrame (m + 1) Pr.i) (faceEmbedding Pr.i ∘ ⇑b) :
        Fin (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) k)) =
      (Fin.cons (incFrame hcs κ hpiece.1 (-EuclideanSpace.single Pr.i (1 : ℝ)))
        (fun j => incFrame hcs κ hpiece.1 (faceEmbedding Pr.i (b j))) :
          Fin (m + 1) → P.TangentSpace) := by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [stdFrame_apply]
    · simp
  rw [hfun]

include hch in
/-- **The same in the charts of Part I's face manifolds**: for face data `D` of corner
coordinates `κ` of `M` for the face `F` (`FaceData`) and `p ∈ F` with `d_M(p) = 1` in its
domain, a basis `b` of `ℝᵐ` is positive for `faceOrientation` read in the face chart
`removeNth i ∘ κ` (`FaceData.pair`) iff `Tι(ιᵢ b₁), …, Tι(ιᵢ b_m)` is positive for `o_{∂M}`. -/
theorem faceOrientation_eq_iff_mem_stratumOrientation_pair (hM : P.IsSubmanifoldOfDim M (m + 1))
    (o : P.SubmanifoldOrientation M (m + 1)) (a : MPolyfold.Faces (subPolyfold hY))
    (κ : CornerCoords (subPolyfold hY) (m + 1)) (D : FaceData κ a.1) (c : a.1)
    {p : a.1} (hp : (p : M) ∈ D.V₁) (hd : (subPolyfold hY).degIndex (p : M) = 1)
    (b : Basis (Fin m) ℝ (EuclideanSpace ℝ (Fin m))) :
    letI := faceChartedSpace hcs hfs a.2
    (b.orientation = orientationIn (D.pair hcs hfs hch a.2 c).eN p
        (faceOrientation hcs hfs (bridgeOrientation hcs o) hch a p) ↔
      (fun j => incFrame hcs κ (D.V₁_subset hp) (faceEmbedding D.i (b j))) ∈
        (o.stratumOrientation hM (hasTameInducedStructure_of_hasCornerStructureOfDim hcs)).frames
          (p : M).1) :=
  faceOrientation_eq_iff_mem_stratumOrientation hcs hfs hch hM o a κ (D.pair hcs hfs hch a.2 c)
    rfl (FaceData.mem_pair_source hcs hfs hch a.2 D c hp) hd (D.V₁_subset hp) b

/-! ### Figure 9.1: the orientation of the open face extends uniquely to the closed face -/

omit inst in
include hcs hfs in
/-- **The points of a face with `d_M = 1` are dense in the face** (the "interior `θ̇` of the
boundary face `θ`", 2021 p. 427): near every point of a face `F` there are points of `F` at which
only the coordinate of `F` vanishes (`exists_coord_one_zero`). -/
theorem dense_faceStratum (a : MPolyfold.Faces (subPolyfold hY)) :
    Dense {q : a.1 | (subPolyfold hY).degIndex (q : M) = 1} := by
  refine dense_iff_inter_open.2 fun U hU ⟨p, hpU⟩ => ?_
  obtain ⟨G', hG', rfl⟩ := isOpen_induced_iff.1 hU
  have hV := mem_faceDataAt_V₁ hcs hfs (p : M) a p.2
  obtain ⟨y, hyG, hys, hyi, hyl⟩ := (hcs.coords (p : M)).exists_coord_one_zero
    (hG'.inter (FaceData.isOpen_V₁ _)) ⟨hpU, hV⟩ (hcs.mem_coords (p : M))
    (faceDataAt_coord hcs hfs (p : M) a p.2)
  have hyF : y ∈ a.1 := FaceData.mem_of_coord_eq_zero _ hyG.2 hyi
  exact ⟨⟨y, hyF⟩, hyG.1, (hcs.coords (p : M)).degIndex_eq_one hys hyi fun l hl => (hyl l hl).ne'⟩

end MPolyfold

section Unique

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] {k : ℕ}

/-- **Two continuous tangent orientations that agree on a dense set are equal**: both are
locally constant in the chart at a point, and `orientationIn` is injective. -/
theorem TangentOrientation.eq_of_eqOn_dense {o₁ o₂ : TangentOrientation I N k}
    (h₁ : o₁.IsContinuous I ∞) (h₂ : o₂.IsContinuous I ∞) {s : Set N} (hs : Dense s)
    (h : ∀ x ∈ s, o₁ x = o₂ x) : o₁ = o₂ := by
  funext x
  by_contra hne
  set e := chartAt H x
  have he := IsManifold.chart_mem_maximalAtlas (I := I) (n := ∞) x
  have hx := mem_chart_source H x
  have hne' : orientationIn e x (o₁ x) ≠ orientationIn e x (o₂ x) := fun h' =>
    hne (tangentOrToModel_injective x (signMap_injective h'))
  have hev := (h₁ e he x hx).and (h₂ e he x hx)
  obtain ⟨y, hys, hy⟩ := hs.inter_nhds_nonempty hev
  apply hne'
  rw [← hy.1, ← hy.2, h y hys]

end Unique

/-- An orientation of `ℝᵏ` is determined by the bases having it. -/
theorem orientation_eq_of_forall_basis {k : ℕ}
    {r₁ r₂ : Orientation ℝ (EuclideanSpace ℝ (Fin k)) (Fin k)}
    (h : ∀ b : Basis (Fin k) ℝ (EuclideanSpace ℝ (Fin k)),
      b.orientation = r₁ ↔ b.orientation = r₂) :
    r₁ = r₂ := by
  classical
  have h0 := h (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  change stdOrientation k = r₁ ↔ stdOrientation k = r₂ at h0
  rw [eq_signedOr_decide r₁, eq_signedOr_decide r₂]
  by_cases h1 : r₁ = stdOrientation k
  · rw [decide_eq_true h1, decide_eq_true (h0.1 h1.symm).symm]
  · have h2 : ¬ r₂ = stdOrientation k := fun h2 => h1 (h0.2 h2.symm).symm
    rw [decide_eq_false h1, decide_eq_false h2]

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {M : Set X} [ParacompactSpace M] {m : ℕ} {hY : P.IsSubMPolyfold M}
  (hcs : (subPolyfold hY).HasCornerStructureOfDim (m + 1))
  (hfs : (subPolyfold hY).IsFaceStructured)
  [inst : ChartedSpace (EuclideanQuadrant (m + 1)) M]
  (hch : inst = (subPolyfold hY).cornerChartedSpace hcs)

/-- **A tangent orientation of the face manifold agrees with `o_{∂M}` at `p`**: in some face
chart pair `(e_F, κ, i)` at `p` with `κ` corner coordinates of `M`, the bases `b` of `ℝᵐ`
positive for it are those whose frames `Tι(ιᵢ b₁), …, Tι(ιᵢ b_m)` are positive for `o_{∂M}`. -/
def IsBoundaryOrientedAt (hM : P.IsSubmanifoldOfDim M (m + 1))
    (o : P.SubmanifoldOrientation M (m + 1)) (a : MPolyfold.Faces (subPolyfold hY)) :
    letI := faceChartedSpace hcs hfs a.2
    TangentOrientation (𝓠 m) a.1 m → a.1 → Prop :=
  letI := faceChartedSpace hcs hfs a.2
  fun oF p => ∃ (Pr : FaceChartPair m (Subtype.val : a.1 → M))
    (κ : CornerCoords (subPolyfold hY) (m + 1)) (_ : Pr.e = κ.toQuadrantChart)
    (_ : p ∈ Pr.eN.source) (hps : (p : M) ∈ κ.s),
    ∀ b : Basis (Fin m) ℝ (EuclideanSpace ℝ (Fin m)),
      b.orientation = orientationIn Pr.eN p (oF p) ↔
        (fun j => incFrame hcs κ hps (faceEmbedding Pr.i (b j))) ∈
          (o.stratumOrientation hM (hasTameInducedStructure_of_hasCornerStructureOfDim hcs)).frames
            (p : M).1

include hch in
/-- `faceOrientation` agrees with `o_{∂M}` at every point of the face with `d_M = 1`. -/
theorem isBoundaryOrientedAt_faceOrientation (hM : P.IsSubmanifoldOfDim M (m + 1))
    (o : P.SubmanifoldOrientation M (m + 1)) (a : MPolyfold.Faces (subPolyfold hY)) {p : a.1}
    (hd : (subPolyfold hY).degIndex (p : M) = 1) :
    IsBoundaryOrientedAt hcs hfs hM o a
      (faceOrientation hcs hfs (bridgeOrientation hcs o) hch a) p := by
  let _ := faceChartedSpace hcs hfs a.2
  set D := faceDataAt hcs hfs (p : M) a p.2
  have hp : (p : M) ∈ D.V₁ := mem_faceDataAt_V₁ hcs hfs (p : M) a p.2
  exact ⟨D.pair hcs hfs hch a.2 p, hcs.coords (p : M), rfl,
    FaceData.mem_pair_source hcs hfs hch a.2 D p hp, D.V₁_subset hp,
    faceOrientation_eq_iff_mem_stratumOrientation_pair hcs hfs hch hM o a _ D p hp hd⟩

include hch in
/-- **Figure 9.1 and the paragraph before it** (2021 p. 427: "this orientation allows one to
extend the orientation of its interior `θ̇` to the boundary of the face"), in Part I's reading
of the closed faces: let `M` be a tame, face-structured `(m+1)`-dimensional submanifold of `X`
oriented by `o` (Definition 9.3.3) and `F` a closed face of `M`, a manifold modelled on
`[0,∞)ᵐ` (`faceChartedSpace`).  There is exactly one continuous tangent orientation of `F` that
agrees with the boundary orientation `o_{∂M}` of Definition 9.3.8 at every point of `F` with
`d_M = 1` (`IsBoundaryOrientedAt`), and it is Part I's induced orientation
`faceOrientation (bridgeOrientation o)` of Theorem 4.4.7. -/
theorem figure_9_1_existsUnique_faceOrientation (hM : P.IsSubmanifoldOfDim M (m + 1))
    (o : P.SubmanifoldOrientation M (m + 1)) (a : MPolyfold.Faces (subPolyfold hY)) :
    letI := faceChartedSpace hcs hfs a.2
    ∃! oF : TangentOrientation (𝓠 m) a.1 m, oF.IsContinuous (𝓠 m) ∞ ∧
      ∀ p : a.1, (subPolyfold hY).degIndex (p : M) = 1 →
        IsBoundaryOrientedAt hcs hfs hM o a oF p := by
  let _ := faceChartedSpace hcs hfs a.2
  have hmanF := isManifold_faceChartedSpace hcs hfs a.2
  have hman := isManifold_of_eq hcs hch
  set fo := faceOrientation hcs hfs (bridgeOrientation hcs o) hch a
  have hfo : fo.IsContinuous (𝓠 m) ∞ := isContinuous_faceOrientation hcs hfs _ hch
    (isContinuous_bridgeOrientation hch (Nat.succ_pos m) hM o) a
  refine ⟨fo, ⟨hfo, fun p hd => isBoundaryOrientedAt_faceOrientation hcs hfs hch hM o a hd⟩,
    fun oF ⟨hoF, hcomp⟩ => ?_⟩
  refine TangentOrientation.eq_of_eqOn_dense hoF hfo (dense_faceStratum hcs hfs a)
    fun p hd => ?_
  obtain ⟨Pr, κ, hPe, hp, hps, hb⟩ := hcomp p hd
  have h' := faceOrientation_eq_iff_mem_stratumOrientation hcs hfs hch hM o a κ Pr hPe hp hd hps
  have := orientation_eq_of_forall_basis fun b => (hb b).trans (h' b).symm
  exact tangentOrToModel_injective p (signMap_injective this)

end MPolyfold

end Polyfold
