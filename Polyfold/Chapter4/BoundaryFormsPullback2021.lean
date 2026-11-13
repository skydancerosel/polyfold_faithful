import Polyfold.Chapter9.SolutionFaceForms2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, **Theorem 6.7.1**
(p. 277–278; preprint Theorem 6.43): the form `p₁^*τ` on the faces of the cobordism `S_F`, for a
form `τ ∈ Ω^*_∞(∂X)` of the relative complex of p. 198 (2017 p. 150; preprint p. 168).

# Forms on `∂X` pulled back to the faces of a finite-dimensional sub-M-polyfold along a map

## The text, paraphrased

(p. 278) On the solution set `S_F ⊆ [0, 1] × X` of the homotopy the text integrates
`p₁^*τ` over `∂S_F`, for `τ ∈ Ω_∞(∂X)` and `p₁ : [0, 1] × X → X` the projection.  This uses,
without comment, that the faces of `S_F` are mapped by `p₁` into the faces of `X`.

## What is formalized

`SolutionFaceForms2021` restricts `τ` to the faces of a sub-M-polyfold `S ⊆ X` (`solFaceForm`).
Here `S` is a sub-M-polyfold of a second tame M-polyfold `X'` (a corner structure of dimension
`n + 1`, `d_S = d_{X'}`), and `G : S → X` is an sc-smooth map with `d_S = d_X ∘ G`
(for `S_F ⊆ ℝ¹ × X` and `G = p₁`: `d_{ℝ¹ × X}(t, x) = d_X(x)`):

* `CornerCoords.zero_coord_face_along`: near a point of the face `{yᵢ = 0}` of corner coordinates
  of `S`, the map `G` takes that face into one face `θ` of a centred admissible triple of `X`.
* `faceAlongData hcs G hX m τ : FaceFormData S n k`, the pull-back `(G^*τ)|_{∂S}`: at a face
  point `q` and face vectors `w`, the value `τ_b(β)` for a linear lift `(b, β)` to `bX^m` of
  `(G^m q, TG^m(κ.fiberMap (ιᵢ w)))` (`linLiftForm`).  For `X' = X` and `G` the inclusion it is
  `solFaceFormData` (`faceAlongData_subIncl`, by definition).
* `isChartFaceForm_faceAlongData`: it is a form on the faces of `S` (smooth, compatible under
  chart changes, agreeing at the corners).
* `isExtendedBy_faceAlongData_formsPullback`: `(G^*η)_S` (`formsAlong`) extends
  `(G^* j^*η)|_{∂S}`; `faceAlongData_formsD`: `(G^* dτ)|_{∂S} = d((G^*τ)|_{∂S})`.

The proofs follow `SolutionFaceForms2021`: the face map `e : U → S` of `FaceLiftData` (for
`S ⊆ X'`) is composed with `G`, and `G ∘ e` lifts to `bX` through `Φ_{(x, V, θ)}⁻¹`.

## The hypotheses

`hX' : PX'.IsTame`, `hdeg' : d_S = d_{X'}` (to reuse the face maps of `FaceLiftData`),
`hX : PX.IsTame`, `hdegG : d_S = d_X ∘ G`.  All hold for the index parts of `S_F` and `G = p₁`
(`CobordismRelativeForms2021`).  No hypothesis quantifies over charts.
-/

open Set Filter Topology Manifold Module WithLp
open scoped ContDiff

noncomputable section

namespace Polyfold

local notation "𝓠" => modelWithCornersEuclideanQuadrant

namespace MPolyfold

universe u v

/-! ### The faces of corner coordinates are mapped into faces of `X` -/

section FacesAlong

open TameBoundary

variable {M : Type u} [TopologicalSpace M] [T2Space M] [ParacompactSpace M] {Q : MPolyfold M}
  {X : Type v} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X} {n : ℕ}

/-- The points of `ℝⁿ` near `y₀` on the face `{yᵢ = 0}` and on no other face. -/
private def faceCell' (y₀ : Fin n → ℝ) (ε : ℝ) (i : Fin n) : Set (Fin n → ℝ) :=
  {y | y ∈ Metric.ball y₀ ε ∧ y i = 0 ∧ ∀ j ≠ i, 0 < y j}

private theorem convex_faceCell' (y₀ : Fin n → ℝ) (ε : ℝ) (i : Fin n) :
    Convex ℝ (faceCell' y₀ ε i) := by
  rintro y ⟨hyB, hyi, hyj⟩ z ⟨hzB, hzi, hzj⟩ a b ha hb hab
  refine ⟨convex_ball y₀ ε hyB hzB ha hb hab, ?_, fun j hj => ?_⟩
  · simp [hyi, hzi]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases ha.lt_or_eq with ha' | rfl
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' (hyj j hj)) (mul_nonneg hb (hzj j hj).le)
    · rw [zero_add] at hab; subst hab; simpa using hzj j hj

private theorem mem_closure_faceCell' {y₀ y y' : Fin n → ℝ} {ε : ℝ} {i : Fin n}
    (hy : y ∈ Metric.ball y₀ ε) (hy0 : ∀ j, 0 ≤ y j) (hyi : y i = 0)
    (hy' : y' ∈ faceCell' y₀ ε i) : y ∈ closure (faceCell' y₀ ε i) := by
  refine closure_mono ?_ (segment_subset_closure_openSegment (left_mem_segment ℝ y y'))
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  refine ⟨(convex_ball y₀ ε).openSegment_subset hy hy'.1 ⟨a, b, ha, hb, hab, rfl⟩, ?_,
    fun j hj => ?_⟩
  · simp [hyi, hy'.2.1]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_pos_of_nonneg_of_pos (mul_nonneg ha.le (hy0 j)) (mul_pos hb (hy'.2.2 j hj))

/-- **A map preserving the degeneracy index takes the faces of corner coordinates into faces of
`X`** (the step "`p₁` maps `∂S_F` to `∂X`" of 2021 p. 278; `CornerCoords.zero_coord_face` for a
map instead of an inclusion): let `κ` be corner coordinates of `Q`, `G : M → X` continuous with
`d_Q = d_X ∘ G`, `X` tame, and `q₀` a point on the face `{yᵢ = 0}` of `κ`.  There is an admissible
boundary triple `t = (G q₀, V, θ)` of `X`, with `V` centred at `G q₀`, and an open `N ∋ q₀` in the
piece of `κ` such that `G` maps the points of `N` on the face `{yᵢ = 0}` into the face `θ`. -/
theorem CornerCoords.zero_coord_face_along (hX : PX.IsTame) {G : M → X} (hG : Continuous G)
    (hdeg : ∀ a : M, Q.degIndex a = PX.degIndex (G a))
    (κ : CornerCoords Q n) {q₀ : M} (hq₀ : q₀ ∈ κ.s) {i : Fin n} (hi : κ.coord q₀ i = 0) :
    ∃ t : BTriple (PX.isCornerIndex_degIndex hX), t.x = G q₀ ∧
      IsCenteredAt PX.degIndex t.x t.V ∧
      ∃ N : Set M, IsOpen N ∧ q₀ ∈ N ∧ N ⊆ κ.s ∧
        ∀ q ∈ N, κ.coord q i = 0 → G q ∈ t.θ := by
  set hd := PX.isCornerIndex_degIndex hX
  set d := PX.degIndex
  have hd1 : 1 ≤ d (G q₀) := (hdeg q₀) ▸ κ.one_le_degIndex hq₀ hi
  obtain ⟨V₀, hV₀⟩ := faceStructuredNbhdsAt_nonempty hd (G q₀)
  set V := reach d V₀ (G q₀) with hVdef
  have hV : V ∈ faceStructuredNbhdsAt d (G q₀) := reach_mem_faceStructuredNbhdsAt hd hV₀
  have hcent : IsCenteredAt d (G q₀) V := isCenteredAt_reach hd hV₀.1.1.1 hV₀.2.1
  have hVo : IsOpen V := hV.1.1.1
  set N₀ : Set M := κ.s ∩ G ⁻¹' V with hN₀
  have hN₀o : IsOpen N₀ := κ.isOpen_s.inter (hVo.preimage hG)
  set y₀ := κ.coord q₀ with hy₀
  have hy₀W : y₀ ∈ κ.W := κ.coord_mem_W hq₀
  have hy₀q : ∀ j, 0 ≤ y₀ j := κ.coord_nonneg hq₀
  have hcw : ContinuousWithinAt κ.coordInv (κ.W ∩ {y | ∀ j, 0 ≤ y j}) y₀ :=
    κ.continuousOn_coordInv y₀ ⟨hy₀W, hy₀q⟩
  have hpre : κ.coordInv ⁻¹' N₀ ∈ 𝓝[κ.W ∩ {y | ∀ j, 0 ≤ y j}] y₀ := by
    refine hcw.preimage_mem_nhdsWithin (hN₀o.mem_nhds ?_)
    rw [hy₀, κ.coordInv_coord hq₀]
    exact ⟨hq₀, hV.2.1⟩
  obtain ⟨u, hu, hy₀u, hus⟩ := mem_nhdsWithin.1 hpre
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hu.inter κ.isOpen_W) y₀ ⟨hy₀u, hy₀W⟩
  have hBW : ∀ y ∈ Metric.ball y₀ ε, y ∈ κ.W := fun y hy => (hball hy).2
  have hBN : ∀ y ∈ Metric.ball y₀ ε, (∀ j, 0 ≤ y j) → κ.coordInv y ∈ N₀ :=
    fun y hy hy0 => hus ⟨(hball hy).1, (hball hy).2, hy0⟩
  set C := faceCell' y₀ ε i with hC
  have hCq : ∀ y ∈ C, y ∈ κ.W ∧ ∀ j, 0 ≤ y j := fun y hy =>
    ⟨hBW y hy.1, fun j => by
      by_cases hj : j = i
      · rw [hj, hy.2.1]
      · exact (hy.2.2 j hj).le⟩
  set y' : Fin n → ℝ := fun j => if j = i then 0 else y₀ j + ε / 2 with hy'
  have hy'C : y' ∈ C := by
    refine ⟨(dist_pi_lt_iff hε).2 fun j => ?_, by simp [hy'], fun j hj => ?_⟩
    · by_cases hj : j = i
      · subst hj; simp [hy', hi, hε]
      · simp only [hy', if_neg hj, Real.dist_eq, add_sub_cancel_left]
        rw [abs_of_pos (half_pos hε)]; exact half_lt_self hε
    · simp only [hy', if_neg hj]; linarith [hy₀q j]
  set K : Set X := G '' (κ.coordInv '' C) with hK
  have hKpre : IsPreconnected K :=
    ((convex_faceCell' y₀ ε i).isPreconnected.image _
      (κ.continuousOn_coordInv.mono fun y hy => hCq y hy)).image _ hG.continuousOn
  have hKsub : K ⊆ V ∩ {z | d z = 1} := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hyq := hCq y hy
    have hN := hBN y hy.1 hyq.2
    refine ⟨hN.2, ?_⟩
    change d (G (κ.coordInv y)) = 1
    rw [← hdeg]
    refine κ.degIndex_eq_one hN.1 (i := i) ?_ fun j hj => ?_
    · rw [κ.coord_coordInv hyq.1 hyq.2]; exact hy.2.1
    · rw [κ.coord_coordInv hyq.1 hyq.2]; exact (hy.2.2 j hj).ne'
  set p : X := G (κ.coordInv y') with hp
  have hpK : p ∈ K := ⟨_, ⟨y', hy'C, rfl⟩, rfl⟩
  have hcc : K ⊆ connectedComponentIn (V ∩ {z | d z = 1}) p :=
    hKpre.subset_connectedComponentIn hpK hKsub
  set N : Set M := κ.s ∩ κ.coord ⁻¹' Metric.ball y₀ ε with hN
  have hNo : IsOpen N := κ.continuousOn_coord.isOpen_inter_preimage κ.isOpen_s Metric.isOpen_ball
  have hq₀N : q₀ ∈ N := ⟨hq₀, Metric.mem_ball_self hε⟩
  have key : ∀ q ∈ N, κ.coord q i = 0 → G q ∈ faceAt d V p := by
    intro q hqN hqi
    have hyB : κ.coord q ∈ Metric.ball y₀ ε := hqN.2
    have hy0 := κ.coord_nonneg hqN.1
    have hycl := mem_closure_faceCell' hyB hy0 hqi hy'C
    have hcwq : ContinuousWithinAt κ.coordInv C (κ.coord q) :=
      (κ.continuousOn_coordInv _ ⟨hBW _ hyB, hy0⟩).mono fun y hy => hCq y hy
    have h1 := hcwq.mem_closure_image hycl
    rw [κ.coordInv_coord hqN.1] at h1
    have h2 : G q ∈ closure K := hG.continuousAt.continuousWithinAt.mem_closure_image h1
    have hqV : G q ∈ V := by
      have := hBN _ hyB hy0
      rw [κ.coordInv_coord hqN.1] at this
      exact this.2
    exact ⟨hqV, closure_mono hcc h2⟩
  have hpV : p ∈ V := (hKsub hpK).1
  have hp1 : d p = 1 := (hKsub hpK).2
  refine ⟨⟨⟨G q₀, V, hV, hd1⟩, faceAt d V p, ⟨⟨p, hpV, hp1, rfl⟩, key q₀ hq₀N hi⟩⟩, rfl, hcent,
    N, hNo, hq₀N, fun _ hq => hq.1, key⟩

end FacesAlong

/-! ### The local data at a face point, along a map `G : S → X` -/

section FaceAlong

open TameBoundary BundledMPolyfold

variable {X' : Type u} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X']
  {PX' : MPolyfold X'} {S : Set X'} [ParacompactSpace S] {hY : PX'.IsSubMPolyfold S} {n : ℕ}
  (hcs : (subPolyfold hY).HasCornerStructureOfDim (n + 1))
  {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  (G : ScMap (subPolyfold hY) (BundledMPolyfold.of PX).P)

/-- **The local data at a face point, along `G`**: local data `D` of `S ⊆ X'` at the face point
(`FaceLiftData`: the face parameters `U` and the face map `e : U → S`), and an admissible
boundary triple `t = (·, V, θ)` of `X` with `V` centred, such that `G ∘ e` takes its values in the
face `θ` (`CornerCoords.zero_coord_face_along`). -/
structure FaceLiftAlong (hX' : PX'.IsTame) (hX : PX.IsTame) (x : S) (i : Fin (n + 1)) where
  /-- The local data of `S ⊆ X'`. -/
  D : FaceLiftData hcs hX' x i
  /-- The admissible boundary triple of `X`. -/
  t : BTriple (PX.isCornerIndex_degIndex hX)
  centred : IsCenteredAt PX.degIndex t.x t.V
  face : ∀ u : D.U, G (D.e u) ∈ t.θ

variable {hcs G}

/-- **The local data exist** at every face point, for tame `X'`, `X` and
`d_S = d_{X'} = d_X ∘ G`. -/
theorem exists_faceLiftAlong (hX' : PX'.IsTame)
    (hdeg' : ∀ a : S, (subPolyfold hY).degIndex a = PX'.degIndex a) (hX : PX.IsTame)
    (hdegG : ∀ a : S, (subPolyfold hY).degIndex a = PX.degIndex (G a)) (x : S) (i : Fin (n + 1))
    {u₀ : EuclideanSpace ℝ (Fin n)} (hu₀ : u₀ ∈ faceDomain (hcs.coords x).toQuadrantChart i) :
    ∃ L : FaceLiftAlong hcs G hX' hX x i, L.D.u₀ = u₀ := by
  obtain ⟨D, rfl⟩ := exists_faceLiftData hX' hdeg' x i hu₀
  obtain ⟨t, -, ht, N, hNo, hq₀N, -, hface⟩ := CornerCoords.zero_coord_face_along hX
    (continuousOn_univ.1 G.isScSmoothMap.continuousOn) hdegG (hcs.coords x)
    ((hcs.coords x).facePoint_mem_s D.u₀_mem) ((hcs.coords x).coord_facePoint_eq_zero D.u₀_mem)
  let D' : FaceLiftData hcs hX' x i := ⟨D.t, D.centred, D.N ∩ N, D.isOpen_N.inter hNo,
    inter_subset_left.trans D.N_subset, fun q hq => D.face q hq.1, D.u₀, D.u₀_mem,
    ⟨D.facePoint_u₀_mem, hq₀N⟩⟩
  exact ⟨⟨D', t, ht, fun u => hface _ (D'.e_mem_N u).2 (D'.coord_e u)⟩, rfl⟩

namespace FaceLiftAlong

variable {hX' : PX'.IsTame} {hX : PX.IsTame} {x : S} {i : Fin (n + 1)}
  (L : FaceLiftAlong hcs G hX' hX x i)

/-- **The lift `g : U → bX`** of `G ∘ e` through `Φ_{(·,V,θ)}⁻¹ : θ → U(·, V, θ) ⊆ bX`. -/
def g (u : L.D.U) : PX.TameBoundarySpace hX :=
  ((phiHomeomorph _ L.centred).symm ⟨G (L.D.e u), L.face u⟩ : PX.TameBoundarySpace hX)

theorem tameBoundaryMap_g (u : L.D.U) : PX.tameBoundaryMap hX (L.g u) = G (L.D.e u) :=
  bMap_phiHomeomorph_symm _ _

/-- **`g : U → bX` is sc-smooth**: `G ∘ e` is sc-smooth into the face `θ`, and `Φ⁻¹` is sc-smooth
(Theorem 2.7.13, `phi_isScDiffeoOn`). -/
theorem isScSmoothMap_g : L.D.Q.IsScSmoothMap (PX.tameBoundaryPolyfold hX) L.g := by
  let _ := PX.paracompactSpace_subtype L.t.θ
  have h1 : L.D.Q.IsScSmoothMap (PX.facePolyfold hX L.t.mem.1.1 L.t.mem_faces.1)
      (fun u => (⟨G (L.D.e u), L.face u⟩ : L.t.θ)) :=
    isScSmoothOn_subPolyfold_of_val _ (G.isScSmoothMap.comp L.D.isScSmoothMap_e)
  exact (PX.phi_isScDiffeoOn hX L.t L.centred).isScSmoothOn_inv.comp h1 (mapsTo_univ _ _)

/-- `g` as an `ScMap` into `bX`. -/
def gMap : ScMap L.D.Q (bdry hX).P := ⟨L.g, L.isScSmoothMap_g⟩

/-- `B ∘ g = G ∘ e`. -/
theorem bdryMap_comp_gMap : (bdryMap hX).comp L.gMap = G.comp L.D.eMap :=
  ScMap.ext_fun fun u => L.tameBoundaryMap_g u

end FaceLiftAlong

/-! ### The pull-back of forms on `∂X` to the faces of `S` along `G` -/

variable (hcs G) (hX : PX.IsTame)

/-- The index raise `G^m : S → X^m` (`alongLift`). -/
abbrev alongIncl (m : ℕ) : ScMap (subPolyfold hY) ((BundledMPolyfold.of PX).lift m).P :=
  alongLift hcs (A := BundledMPolyfold.of PX) G m

/-- The point `G^m q ∈ (X^m)¹` over `q ∈ S`. -/
abbrev alongPt (m : ℕ) (q : S) : ((BundledMPolyfold.of PX).lift m).P.Level 1 :=
  liftLevelOneMap (alongIncl hcs G m).isScSmoothMap (hcs.levelOne q)

/-- **The face vectors in `TX^m`**: `v ↦ TG^m(κ.fiberMap v)` at `q`, linear in `v ∈ ℝⁿ⁺¹`. -/
def alongVec (m : ℕ) (κ : CornerCoords (subPolyfold hY) (n + 1)) {q : S} (hq : q ∈ κ.s) :
    EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ((BundledMPolyfold.of PX).lift m).P.tangentFiber
      (alongPt hcs G m q) :=
  (tangentFiberMap (alongIncl hcs G m).isScSmoothMap (hcs.levelOne q) :
    _ →ₗ[ℝ] _) ∘ₗ κ.fiberMap (x := hcs.levelOne q) (κ.s_subset hq)

theorem coe_alongVec (m : ℕ) (κ : CornerCoords (subPolyfold hY) (n + 1)) {q : S} (hq : q ∈ κ.s)
    (v : EuclideanSpace ℝ (Fin (n + 1))) :
    (alongVec hcs G m κ hq v).1 = tangentMap (alongIncl hcs G m).isScSmoothMap
      (κ.fiberMap (x := hcs.levelOne q) (κ.s_subset hq) v).1 :=
  coe_tangentFiberMap_apply _ _

variable {k : ℕ}

open scoped Classical in
/-- **The pull-back along `G` of `τ ∈ Ω^k(bX^m)` to the faces of `S`** (2021 p. 278, the form
`p₁^*τ` on `∂S_F`): on the face `{yᵢ = 0}` of the corner chart at `x`, at the point `q` with face
parameter `u` and on the face vectors `w`, the value `τ_b(β)` for a linear lift `(b, β)` of
`(G^m q, TG^m(κ.fiberMap (ιᵢ w)))` to `bX^m` (`linLiftForm`); `0` off the face domain. -/
def faceAlongData (m : ℕ) (τ : (bdry hX).forms k m) : FaceFormData S n k := fun x i u =>
  if hu : u ∈ faceDomain (hcs.coords x).toQuadrantChart i then
    altCont (linLiftForm (bdryMapLift hX m) τ.1
      (alongPt hcs G m (facePoint (hcs.coords x).toQuadrantChart i u))
      (alongVec hcs G m (hcs.coords x) ((hcs.coords x).facePoint_mem_s hu) ∘ₗ
        (faceEmbedding i).toLinearMap))
  else 0

theorem faceAlongData_apply_of_mem (m : ℕ) (τ : (bdry hX).forms k m) (x : S) (i : Fin (n + 1))
    {u : EuclideanSpace ℝ (Fin n)} (hu : u ∈ faceDomain (hcs.coords x).toQuadrantChart i)
    (w : Fin k → EuclideanSpace ℝ (Fin n)) :
    faceAlongData hcs G hX m τ x i u w = linLiftForm (bdryMapLift hX m) τ.1
      (alongPt hcs G m (facePoint (hcs.coords x).toQuadrantChart i u))
      (alongVec hcs G m (hcs.coords x) ((hcs.coords x).facePoint_mem_s hu) ∘ₗ
        (faceEmbedding i).toLinearMap) w := by
  rw [faceAlongData, dif_pos hu]; rfl

theorem faceAlongData_apply_of_notMem (m : ℕ) (τ : (bdry hX).forms k m) (x : S)
    (i : Fin (n + 1)) {u : EuclideanSpace ℝ (Fin n)}
    (hu : u ∉ faceDomain (hcs.coords x).toQuadrantChart i) :
    faceAlongData hcs G hX m τ x i u = 0 := by
  rw [faceAlongData, dif_neg hu]

theorem faceAlongData_add (m : ℕ) (τ σ : (bdry hX).forms k m) :
    faceAlongData hcs G hX m (τ + σ) =
      faceAlongData hcs G hX m τ + faceAlongData hcs G hX m σ := by
  funext x i u
  by_cases hu : u ∈ faceDomain (hcs.coords x).toQuadrantChart i
  · ext w
    rw [Pi.add_apply, Pi.add_apply, Pi.add_apply, ContinuousAlternatingMap.add_apply,
      faceAlongData_apply_of_mem _ _ _ _ _ _ _ hu, faceAlongData_apply_of_mem _ _ _ _ _ _ _ hu,
      faceAlongData_apply_of_mem _ _ _ _ _ _ _ hu]
    change linLiftForm _ (τ.1 + σ.1) _ _ w = _
    rw [linLiftForm_add]
    rfl
  · simp only [Pi.add_apply, faceAlongData_apply_of_notMem _ _ _ _ _ _ _ hu, add_zero]

theorem faceAlongData_smul (m : ℕ) (c : ℝ) (τ : (bdry hX).forms k m) :
    faceAlongData hcs G hX m (c • τ) = c • faceAlongData hcs G hX m τ := by
  funext x i u
  by_cases hu : u ∈ faceDomain (hcs.coords x).toQuadrantChart i
  · ext w
    rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
      faceAlongData_apply_of_mem _ _ _ _ _ _ _ hu, faceAlongData_apply_of_mem _ _ _ _ _ _ _ hu]
    change linLiftForm _ (c • τ.1) _ _ w = _
    rw [linLiftForm_smul]
    rfl
  · simp only [Pi.smul_apply, faceAlongData_apply_of_notMem _ _ _ _ _ _ _ hu, smul_zero]

theorem faceAlongData_zero (m : ℕ) :
    faceAlongData hcs G hX m (0 : (bdry hX).forms k m) = 0 := by
  have h := faceAlongData_smul hcs G hX m (0 : ℝ) (0 : (bdry hX).forms k m)
  rwa [zero_smul, zero_smul] at h

namespace FaceLiftAlong

variable {hcs G hX} {hX' : PX'.IsTame} {x : S} {i : Fin (n + 1)}
  (L : FaceLiftAlong hcs G hX' hX x i)

/-- **The linear lift at `u ∈ U`**: `b = g^m(u)` and `L = Tg^m ∘ κ_U.fiberMap`. -/
theorem isLinLift (m : ℕ) (u : L.D.U) :
    IsLinLift (bdryMapLift hX m) (alongPt hcs G m (L.D.e u))
      (alongVec hcs G m (hcs.coords x) (L.D.e_mem_s u) ∘ₗ (faceEmbedding i).toLinearMap)
      (liftLevelOneMap (alongLift L.D.hcsQ L.gMap m).isScSmoothMap (L.D.hcsQ.levelOne u))
      ((tangentFiberMap (alongLift L.D.hcsQ L.gMap m).isScSmoothMap (L.D.hcsQ.levelOne u) :
        _ →ₗ[ℝ] _) ∘ₗ L.D.κQ.fiberMap (x := L.D.hcsQ.levelOne u) (L.D.κQ.s_subset (mem_univ _)))
    where
  base := by
    change (bdry hX).liftMap (bdryMap hX) m (alongLift L.D.hcsQ L.gMap m u) =
      alongIncl hcs G m (L.D.e u)
    rw [liftMap_alongLift L.D.hcsQ L.gMap (bdryMap hX) m u, L.bdryMap_comp_gMap]
    exact alongLift_comp (A := BundledMPolyfold.of PX) L.D.hcsQ hcs G L.D.eMap m u
  vec := fun w => by
    change tangentMap (bdryMapLift hX m)
      (tangentFiberMap (alongLift L.D.hcsQ L.gMap m).isScSmoothMap
      (L.D.hcsQ.levelOne u) (L.D.κQ.fiberMap (L.D.κQ.s_subset (mem_univ _)) w)).1 =
      (alongVec hcs G m (hcs.coords x) (L.D.e_mem_s u) (faceEmbedding i w)).1
    have hfun : ⇑((bdry hX).liftMap (bdryMap hX) m) ∘ ⇑(alongLift L.D.hcsQ L.gMap m) =
        ⇑(alongIncl hcs G m) ∘ L.D.e := by
      funext u
      rw [Function.comp_apply, liftMap_alongLift L.D.hcsQ L.gMap (bdryMap hX) m u,
        L.bdryMap_comp_gMap]
      exact alongLift_comp (A := BundledMPolyfold.of PX) L.D.hcsQ hcs G L.D.eMap m u
    rw [coe_tangentFiberMap_apply, coe_alongVec, ← Function.comp_apply
        (f := tangentMap (bdryMapLift hX m)),
      ← tangentMap_comp (bdryMapLift hX m) (alongLift L.D.hcsQ L.gMap m).isScSmoothMap,
      tangentMap_congr_fun ((bdryMapLift hX m).comp (alongLift L.D.hcsQ L.gMap m).isScSmoothMap)
        ((alongIncl hcs G m).isScSmoothMap.comp L.D.isScSmoothMap_e) hfun,
      tangentMap_comp (alongIncl hcs G m).isScSmoothMap L.D.isScSmoothMap_e, Function.comp_apply,
      L.D.tangentMap_e_fiberMap]

/-- **The key identity**: on `U`, the face form of `τ` along `G` is the pull-back `(g^m)^*τ` of
`τ` along `g : U → bX`, read in the standard chart of `U` (`formsAlong`). -/
theorem faceAlongData_eq_chartForm (m : ℕ) {τ : (bdry hX).forms k m}
    (hτ : IsFaceCompatible hX m τ.1) {u : EuclideanSpace ℝ (Fin n)} (hu : u ∈ L.D.U) :
    faceAlongData hcs G hX m τ x i u =
      ManifoldForm.chartForm (𝓠 n) L.D.κQ.toQuadrantChart (formsAlong L.D.hcsQ L.gMap m τ) u := by
  ext w
  have hy : u ∈ (L.D.κQ.toQuadrantChart.extend (𝓠 n)).target := by
    rw [quadrantPieceCoords_extend_target]; exact hu
  rw [faceAlongData_apply_of_mem _ _ _ _ _ _ _ (L.D.U_subset_faceDomain hu)]
  change linLiftForm (bdryMapLift hX m) τ.1 (alongPt hcs G m (L.D.e ⟨u, hu⟩))
    (alongVec hcs G m (hcs.coords x) (L.D.e_mem_s ⟨u, hu⟩) ∘ₗ (faceEmbedding i).toLinearMap) w = _
  rw [linLiftForm_eq hτ (L.isLinLift m ⟨u, hu⟩), formsAlong_apply,
    chartForm_cornerForm_fiberMap L.D.hcsQ rfl L.D.κQ _ hy w]
  have hsymm : (L.D.κQ.toQuadrantChart.extend (𝓠 n)).symm u = ⟨u, hu⟩ :=
    quadrantPieceCoords_extend_symm _ _ hu
  change formPullback _ τ.1 (L.D.hcsQ.levelOne ⟨u, hu⟩) (fun j => L.D.κQ.fiberMap _ (w j)) = _
  rw [formPullback_apply]
  refine altFamily_congr τ.1 (congrArg _ (congrArg L.D.hcsQ.levelOne hsymm.symm)) _ _ fun j => ?_
  beta_reduce
  rw [coe_tangentFiberMap_apply]
  exact (congrArg (tangentMap _)
    (L.D.κQ.coe_fiberMap_congr (congrArg L.D.hcsQ.levelOne hsymm.symm) _ _ (w j))).trans
    (coe_tangentFiberMap_apply _ _).symm

end FaceLiftAlong

/-! ### The face forms along `G`: smoothness, chart changes, corners, `d` -/

variable (hX' : PX'.IsTame) (hdeg' : ∀ a : S, (subPolyfold hY).degIndex a = PX'.degIndex a)
  (hdegG : ∀ a : S, (subPolyfold hY).degIndex a = PX.degIndex (G a))
include hX' hdeg' hdegG

/-- Lifts exist at every face point. -/
theorem exists_isLinLift_facePoint_along (m : ℕ) (x : S) (i : Fin (n + 1))
    {u : EuclideanSpace ℝ (Fin n)} (hu : u ∈ faceDomain (hcs.coords x).toQuadrantChart i) :
    ∃ (b : ((bdry hX).lift m).P.Level 1)
      (L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ((bdry hX).lift m).P.tangentFiber b),
      IsLinLift (bdryMapLift hX m)
        (alongPt hcs G m (facePoint (hcs.coords x).toQuadrantChart i u))
        (alongVec hcs G m (hcs.coords x) ((hcs.coords x).facePoint_mem_s hu) ∘ₗ
          (faceEmbedding i).toLinearMap) b L := by
  obtain ⟨L, rfl⟩ := exists_faceLiftAlong hX' hdeg' hX hdegG x i hu
  exact ⟨_, _, L.isLinLift m ⟨L.D.u₀, L.D.mem_U_iff.2 ⟨L.D.u₀_mem, L.D.facePoint_u₀_mem⟩⟩⟩

/-- **The face forms along `G` are `C^∞`** (locally `(g^m)^*τ`). -/
theorem contDiffOn_faceAlongData (m : ℕ) {τ : (bdry hX).forms k m}
    (hτ : IsFaceCompatible hX m τ.1) (x : S) (i : Fin (n + 1)) :
    ContDiffOn ℝ ∞ (faceAlongData hcs G hX m τ x i)
      (faceDomain (hcs.coords x).toQuadrantChart i) := by
  intro u hu
  obtain ⟨L, rfl⟩ := exists_faceLiftAlong hX' hdeg' hX hdegG x i hu
  have huU : L.D.u₀ ∈ L.D.U := L.D.mem_U_iff.2 ⟨L.D.u₀_mem, L.D.facePoint_u₀_mem⟩
  have h1 : ContDiffOn ℝ ∞ (ManifoldForm.chartForm (𝓠 n) L.D.κQ.toQuadrantChart
      (formsAlong L.D.hcsQ L.gMap m τ)) L.D.U := by
    have h := contDiffOn_chartForm_cornerForm rfl L.D.κQ
      (formPullback_mem_scForms (alongLift L.D.hcsQ L.gMap m).isScSmoothMap τ.2)
    rw [quadrantPieceCoords_extend_target] at h
    exact h
  refine ((h1.congr fun z hz => ?_) L.D.u₀ huU).mono_of_mem_nhdsWithin (L.D.U_mem_nhdsWithin huU)
  exact L.faceAlongData_eq_chartForm m hτ hz

variable [inst : ChartedSpace (EuclideanQuadrant (n + 1)) S]
  (hch : inst = (subPolyfold hY).cornerChartedSpace hcs)
include hch

/-- **`(G^*η)_S` extends `(G^* j^*η)|_{∂S}`** (`j^* = B^*`): on the face vectors, both are `η` at
`TG^m(κ.fiberMap (ιᵢ w))`. -/
theorem isExtendedBy_faceAlongData_formsPullback (m : ℕ)
    (η : (BundledMPolyfold.of PX).forms k m) :
    IsExtendedBy (faceAlongData hcs G hX m (formsPullback (bdryMap hX) k m η))
      (formsAlong hcs (A := BundledMPolyfold.of PX) G m η) := by
  intro x i u hu
  rw [chartAt_eq_coords hcs hch] at hu
  obtain ⟨b, L, hl⟩ := exists_isLinLift_facePoint_along hcs G hX hX' hdeg' hdegG m x i hu
  ext w
  rw [faceRestriction_apply, chartAt_eq_coords hcs hch,
    faceAlongData_apply_of_mem _ _ _ _ _ _ _ hu, coe_formsPullback, linLiftForm_formPullback _ hl]
  exact (chartForm_cornerForm_fiberMap hcs hch (hcs.coords x) _ hu (faceEmbedding i ∘ w)).trans
    rfl

/-- **`(G^* dτ)|_{∂S} = d((G^*τ)|_{∂S})`** (`extDeriv_formsAlong` on each piece `U`). -/
theorem faceAlongData_formsD (m : ℕ) {τ : (bdry hX).forms k m} (hτ : τ ∈ bForms hX k m) :
    faceAlongData hcs G hX (m + 1) ((bdry hX).formsD k m τ) =
      FaceFormData.d (faceAlongData hcs G hX m τ) := by
  funext x i u
  by_cases hu : u ∈ faceDomain (hcs.coords x).toQuadrantChart i
  · have huc : u ∈ faceDomain (chartAt (EuclideanQuadrant (n + 1)) x) i := by
      rw [chartAt_eq_coords hcs hch]; exact hu
    obtain ⟨L, rfl⟩ := exists_faceLiftAlong hX' hdeg' hX hdegG x i hu
    have huU : L.D.u₀ ∈ L.D.U := L.D.mem_U_iff.2 ⟨L.D.u₀_mem, L.D.facePoint_u₀_mem⟩
    have hy : L.D.u₀ ∈ (L.D.κQ.toQuadrantChart.extend (𝓠 n)).target := by
      rw [quadrantPieceCoords_extend_target]; exact huU
    rw [FaceFormData.d_apply_of_mem _ huc, chartAt_eq_coords hcs hch,
      L.faceAlongData_eq_chartForm (m + 1) (extD_mem_bForms hX k hτ).1 huU,
      ← extDeriv_formsAlong L.gMap rfl m τ,
      ManifoldForm.chartForm_extDeriv_of_mem_target (mem_maximalAtlas_of_eq L.D.hcsQ rfl L.D.κQ)
        ((contMDiffForm_formsAlong L.gMap rfl m τ).of_le (by exact_mod_cast le_top)) hy,
      quadrantPieceCoords_extend_target]
    have h1 : extDerivWithin (faceAlongData hcs G hX m τ x i)
        (faceDomain (hcs.coords x).toQuadrantChart i) L.D.u₀ =
        extDerivWithin (faceAlongData hcs G hX m τ x i) L.D.U L.D.u₀ := by
      unfold extDerivWithin
      rw [fderivWithin_congr_set (L.D.U_eventuallyEq_faceDomain huU)]
    rw [h1]
    exact Filter.EventuallyEq.extDerivWithin_eq_of_mem (eventually_nhdsWithin_of_forall
      fun z hz => (L.faceAlongData_eq_chartForm m hτ.1 hz).symm) huU
  · have huc : u ∉ faceDomain (chartAt (EuclideanQuadrant (n + 1)) x) i := by
      rw [chartAt_eq_coords hcs hch]; exact hu
    rw [faceAlongData_apply_of_notMem _ _ _ _ _ _ _ hu]
    exact (FaceFormData.d_apply_of_notMem _ huc).symm

/-- **`(G^*τ)|_{∂S}` is a form on the faces of `S`** (`IsChartFaceForm`): smooth, compatible
under chart changes and agreeing at the corners (the last two from the agreement of `τ` over
`B`). -/
theorem isChartFaceForm_faceAlongData (m : ℕ) {τ : (bdry hX).forms k m}
    (hτ : τ ∈ bForms hX k m) : IsChartFaceForm (faceAlongData hcs G hX m τ) where
  smooth x i := by
    rw [chartAt_eq_coords hcs hch]
    exact contDiffOn_faceAlongData hcs G hX hX' hdeg' hdegG m hτ.1 x i
  chartChange x x' p hp hp' i i' hi hi' w := by
    have := isManifold_of_eq hcs hch
    have hc := mem_maximalAtlas_of_eq hcs hch (hcs.coords x)
    have hc' := mem_maximalAtlas_of_eq hcs hch (hcs.coords x')
    simp only [chartAt_eq_coords hcs hch] at hp hp' hi hi' ⊢
    obtain ⟨j, hj, hA, -⟩ := exists_face_chartChange hc hc' hp hp' hi
    obtain rfl : j = i' := (hi' j).1 ((hj j).2 rfl)
    have hu : faceProjection i ((hcs.coords x).toQuadrantChart.extend (𝓠 (n + 1)) p) ∈
        faceDomain (hcs.coords x).toQuadrantChart i :=
      faceProjection_extend_mem_faceDomain hp ((hi i).2 rfl)
    have hu' : faceProjection j ((hcs.coords x').toQuadrantChart.extend (𝓠 (n + 1)) p) ∈
        faceDomain (hcs.coords x').toQuadrantChart j :=
      faceProjection_extend_mem_faceDomain hp' ((hj j).2 rfl)
    have hq : facePoint (hcs.coords x).toQuadrantChart i
        (faceProjection i ((hcs.coords x).toQuadrantChart.extend (𝓠 (n + 1)) p)) = p :=
      facePoint_faceProjection_extend hp ((hi i).2 rfl)
    have hq' : facePoint (hcs.coords x').toQuadrantChart j
        (faceProjection j ((hcs.coords x').toQuadrantChart.extend (𝓠 (n + 1)) p)) = p :=
      facePoint_faceProjection_extend hp' ((hj j).2 rfl)
    rw [faceAlongData_apply_of_mem _ _ _ _ _ _ _ hu',
      faceAlongData_apply_of_mem _ _ _ _ _ _ _ hu]
    refine linLiftForm_apply_congr hτ.1 (congrArg (alongPt hcs G m) (hq'.trans hq.symm))
      (exists_isLinLift_facePoint_along hcs G hX hX' hdeg' hdegG m x' j hu')
      (exists_isLinLift_facePoint_along hcs G hX hX' hdeg' hdegG m x i hu) _ _ fun l => ?_
    change (alongVec hcs G m (hcs.coords x') ((hcs.coords x').facePoint_mem_s hu')
      (faceEmbedding j (faceRestrict (chartChangeDeriv (𝓠 (n + 1)) (hcs.coords x).toQuadrantChart
        (hcs.coords x').toQuadrantChart p) i j (w l)))).1 =
      (alongVec hcs G m (hcs.coords x) ((hcs.coords x).facePoint_mem_s hu)
        (faceEmbedding i (w l))).1
    rw [← apply_faceEmbedding_eq (fun y => hA _ (faceEmbedding_apply_self i y)) (w l),
      coe_alongVec, coe_alongVec]
    exact congrArg (tangentMap _)
      (((hcs.coords x').coe_fiberMap_congr (congrArg hcs.levelOne hq') _ _ _).trans
        ((congrArg Subtype.val
          (fiberMap_chartChange hch (hcs.coords x) (hcs.coords x') hp hp'
            (faceEmbedding i (w l)))).trans
          ((hcs.coords x).coe_fiberMap_congr (congrArg hcs.levelOne hq.symm) _ _ _)))
  corner x i j y hy hyi hyj v hvi hvj := by
    rw [chartAt_eq_coords hcs hch] at hy
    have hui : faceProjection i y ∈ faceDomain (hcs.coords x).toQuadrantChart i :=
      faceProjection_mem_faceDomain hy hyi
    have huj : faceProjection j y ∈ faceDomain (hcs.coords x).toQuadrantChart j :=
      faceProjection_mem_faceDomain hy hyj
    have hqi : facePoint (hcs.coords x).toQuadrantChart i (faceProjection i y) =
        ((hcs.coords x).toQuadrantChart.extend (𝓠 (n + 1))).symm y := facePoint_faceProjection hyi
    have hqj : facePoint (hcs.coords x).toQuadrantChart j (faceProjection j y) =
        ((hcs.coords x).toQuadrantChart.extend (𝓠 (n + 1))).symm y := facePoint_faceProjection hyj
    rw [faceLift_apply, faceLift_apply, faceAlongData_apply_of_mem _ _ _ _ _ _ _ hui,
      faceAlongData_apply_of_mem _ _ _ _ _ _ _ huj]
    refine linLiftForm_apply_congr hτ.1 (congrArg (alongPt hcs G m) (hqi.trans hqj.symm))
      (exists_isLinLift_facePoint_along hcs G hX hX' hdeg' hdegG m x i hui)
      (exists_isLinLift_facePoint_along hcs G hX hX' hdeg' hdegG m x j huj) _ _ fun l => ?_
    change (alongVec hcs G m (hcs.coords x) ((hcs.coords x).facePoint_mem_s hui)
        (faceEmbedding i (faceProjection i (v l)))).1 =
      (alongVec hcs G m (hcs.coords x) ((hcs.coords x).facePoint_mem_s huj)
        (faceEmbedding j (faceProjection j (v l)))).1
    rw [faceEmbedding_faceProjection (hvi l), faceEmbedding_faceProjection (hvj l), coe_alongVec,
      coe_alongVec]
    exact congrArg (tangentMap _)
      ((hcs.coords x).coe_fiberMap_congr (congrArg hcs.levelOne (hqi.trans hqj.symm)) _ _ _)

end FaceAlong

/-! ### The inclusion: `solFaceFormData` -/

section SubIncl

open BundledMPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {S : Set X} [ParacompactSpace S] {hY : PX.IsSubMPolyfold S} {n k : ℕ}
  (hcs : (subPolyfold hY).HasCornerStructureOfDim (n + 1)) (hX : PX.IsTame)

/-- For the inclusion `S ⊆ X`, the face forms along `G` are the restriction `solFaceFormData` of
`SolutionFaceForms2021` (by definition). -/
theorem faceAlongData_subIncl (m : ℕ) (τ : (bdry hX).forms k m) :
    faceAlongData hcs (subInclScMap hY) hX m τ = solFaceFormData hcs hX m τ :=
  rfl

end SubIncl

end MPolyfold

end Polyfold
