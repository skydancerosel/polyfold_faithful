import Polyfold.Chapter4.ManifoldFaceForms2021
import Polyfold.Chapter4.BoundaryForms2021
import Polyfold.Chapter9.MathlibFormsBridge2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, **Theorem 6.7.1**
(p. 277; preprint Theorem 6.43), the boundary term `∫_{∂S_{f+s}} τ` of `Ψ_{(f,o)}`, and the
relative complex of p. 198 (2017 p. 150; preprint p. 168).

# The faces of a solution set and the faces of `X`

## The text, paraphrased

(p. 277) For a perturbation `s` in general position, `S_{f+s}` is a compact manifold with boundary
with corners, and for `[ω, τ] ∈ H*_dR(X, ∂X)` the number `∫_{S_{f+s}} ω − ∫_{∂S_{f+s}} τ` is the
invariant.  The form `τ` lives on `∂X` (p. 198: on the local faces of `X` and their
intersections), so `∫_{∂S} τ` needs the faces of `S` to lie in the faces of `X`.

## What is formalized

* **The degeneracy index in corner coordinates**: for any corner coordinates `κ` of an
  M-polyfold `Q` (`CornerCoords`, the charts of `cornerChartedSpace`), `d_Q(x)` is the number of
  vanishing coordinates of `κ.coord x` (`CornerCoords.degIndex_eq_card`; Theorem 1.3.5 for the
  affine coordinate change `v ↦ Ψ v + c`).
* **The faces of `S` are cut out by the faces of `X`** (`CornerCoords.zero_coord_face`): for a
  sub-M-polyfold `S` of a tame `X` with `d_S = d_X` on `S` (true for the solution sets in general
  position, `theorem_6_6_18_solutionSet`), a point `q₀` on the face `{yᵢ = 0}` of corner
  coordinates `κ` of `S` gives an admissible boundary triple `t = (q₀, V, θ)` of `X`
  (2021 Definition 2.7.10) with `V` centred at `q₀`, such that every point of the face `{yᵢ = 0}`
  of `κ` near `q₀` lies on the face `θ` of `V`; it has a unique lift to `U(t) ⊆ bX`
  (`CornerCoords.exists_lift_uSet`).

## What the text leaves implicit, and the choices made

* The text takes for granted that the faces of `S_{f+s}` lie in the faces of `X`.  We prove it
  from `d_S = d_X` (general position, Theorem 4.2.11) and the definition of the faces of `V`
  (closures of components of `{d_X = 1} ∩ V`): near `q₀` the points of the face `{yᵢ = 0}` with no
  other vanishing coordinate form a convex, hence connected, set of points with `d_X = 1`.
* The corner coordinates of `cornerChartedSpace` are arbitrary corner coordinates (a choice), so
  the statements are proved for all corner coordinates; no restriction of the atlas is needed.
* Only the inclusion "face of `S` ⊆ face of `X`" near a point is proved; it is what the boundary
  term needs.  The restriction of a form on `∂X` to the faces of `S` (a tangent-level statement)
  is not in this file.
-/

open Set Filter Topology Manifold Module WithLp
open scoped ContDiff

noncomputable section

namespace Polyfold

/-! ### The quadrant `[0,∞)ⁿ` as a presented partial quadrant -/

section StdQuadrant

/-- The presentation `ℝⁿ ≅ ℝⁿ ⊕ ℝ⁰` of the quadrant `[0,∞)ⁿ ⊆ ℝⁿ` (constant sc-structures). -/
def stdQuadrantPres (n : ℕ) :
    ScIso (ScBanach.const (Fin n → ℝ))
      ((ScBanach.const (Fin n → ℝ)).prod (ScBanach.const (Fin 0 → ℝ))) where
  lvl _ := (ContinuousLinearEquiv.prodUnique ℝ (Fin n → ℝ) (Fin 0 → ℝ)).symm
  incl_comm _ _ := Prod.ext rfl (funext fun i => i.elim0)

theorem stdQuadrant_eq (n : ℕ) : {y : Fin n → ℝ | ∀ i, 0 ≤ y i} =
    (stdQuadrantPres n) 0 ⁻¹' quadrant n (ScBanach.const (Fin 0 → ℝ)) 0 :=
  rfl

/-- `[0,∞)ⁿ ⊆ ℝⁿ` (the constant structure) is a partial quadrant. -/
theorem isPartialQuadrant_stdQuadrant (n : ℕ) :
    IsPartialQuadrant (ScBanach.const (Fin n → ℝ)) {y : Fin n → ℝ | ∀ i, 0 ≤ y i} :=
  ⟨n, _, stdQuadrantPres n, stdQuadrant_eq n⟩

/-- `W ∩ [0,∞)ⁿ` is relatively open in the quadrant for open `W ⊆ ℝⁿ`. -/
theorem isRelOpenInQuadrant_stdQuadrant {n : ℕ} {W : Set (Fin n → ℝ)} (hW : IsOpen W) :
    IsRelOpenInQuadrant (ScBanach.const (Fin n → ℝ)) {y : Fin n → ℝ | ∀ i, 0 ≤ y i}
      (W ∩ {y | ∀ i, 0 ≤ y i}) :=
  ⟨isPartialQuadrant_stdQuadrant n, W, hW, rfl⟩

/-- **The degeneracy index of `[0,∞)ⁿ`** (Definition 1.3.3) is the number of vanishing
coordinates. -/
theorem degIndex_stdQuadrant {n : ℕ} {y : Fin n → ℝ} (hy : ∀ i, 0 ≤ y i) :
    Polyfold.degIndex (ScBanach.const (Fin n → ℝ)) {y : Fin n → ℝ | ∀ i, 0 ≤ y i} y =
      (Finset.univ.filter fun i => y i = 0).card :=
  degIndex_eq (stdQuadrantPres n) (stdQuadrant_eq n) hy

end StdQuadrant

/-! ### Sc-smoothness into a finite-dimensional model -/

section FiniteDimTarget

variable {E F : ScBanach} [FiniteDimensional ℝ (F 0)] {U : Set (E 0)} {f : E 0 → F 0}

/-- A `C^∞` map from the constant structure of a finite-dimensional space into a model `F` with
finite-dimensional `F₀` is sc-smooth (the levels of `F` are all `F₀`,
`isoConstOfFiniteDimensional`). -/
theorem isScSmooth_of_contDiffOn_const_finiteDim {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {U : Set V} (hU : IsScDomain (ScBanach.const V) U)
    {g : V → F 0} (h : ContDiffOn ℝ ∞ g U) :
    IsScSmooth (E := ScBanach.const V) (F := F) U g := by
  refine IsScSmooth.of_contDiffOn_levels hU
    (fun m _ _ => (F.toBase_bijective_of_finiteDimensional m).2 _) fun m => ?_
  set e := F.isoConstOfFiniteDimensional m
  have heq : EqOn (levelMap (E := ScBanach.const V) (F := F) g m) (fun x => e.symm (g x))
      ((ScBanach.const V).lvlSet U m) := fun x _ => by
    refine levelMap_eq_of_toBase_eq ?_
    rw [← ScBanach.isoConstOfFiniteDimensional_apply, ContinuousLinearEquiv.apply_symm_apply,
      ScBanach.const_toBase]
  have hlvl : (ScBanach.const V).lvlSet U m = U := by
    ext x
    rw [ScBanach.mem_lvlSet, ScBanach.const_toBase]
  refine ContDiffOn.congr ?_ heq
  rw [hlvl]
  exact e.symm.contDiff.comp_contDiffOn h

end FiniteDimTarget

local notation "𝓠" => modelWithCornersEuclideanQuadrant

namespace MPolyfold

universe u

/-! ### The degeneracy index in corner coordinates -/

namespace CornerCoords

variable {M : Type u} [TopologicalSpace M] [T2Space M] [ParacompactSpace M] {Q : MPolyfold M}
  {n : ℕ} (κ : CornerCoords Q n)

/-- The image `χ(s)` of the coordinate piece is relatively open in the partial quadrant of `χ`. -/
theorem isRelOpenInQuadrant_image_s :
    IsRelOpenInQuadrant κ.χ.model.E κ.χ.model.C (κ.χ '' κ.s) := by
  obtain ⟨W₀, hW₀, h⟩ := κ.χ.exists_isOpen_image_eq κ.s_subset κ.isOpen_s
  rw [h]
  exact κ.isCornerChart.isRelOpenInQuadrant.inter_isOpen hW₀

/-- The affine coordinates `v ↦ Ψ v + c` are sc-smooth on `χ(s)`. -/
theorem isScSmooth_coordAff :
    IsScSmooth (E := κ.χ.model.E) (F := ScBanach.const (Fin n → ℝ)) (κ.χ '' κ.s)
      (fun v => κ.Ψ v + κ.c) := by
  have := κ.isCornerChart.finiteDimensional
  exact IsScSmooth.of_contDiffOn_finiteDimensional κ.isRelOpenInQuadrant_image_s.isScDomain
    (κ.Ψ.contDiff.add contDiff_const).contDiffOn

/-- The inverse affine coordinates `y ↦ Ψ⁻¹(y − c)` are sc-smooth on `W ∩ [0,∞)ⁿ`. -/
theorem isScSmooth_coordAffInv :
    IsScSmooth (E := ScBanach.const (Fin n → ℝ)) (F := κ.χ.model.E) (κ.W ∩ {y | ∀ i, 0 ≤ y i})
      (fun y => κ.Ψ.symm (y - κ.c)) := by
  have := κ.isCornerChart.finiteDimensional
  exact isScSmooth_of_contDiffOn_const_finiteDim
    (isRelOpenInQuadrant_stdQuadrant κ.isOpen_W).isScDomain
    (κ.Ψ.symm.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn

/-- **The degeneracy index in corner coordinates**: `d_Q(x)` is the number of vanishing
coordinates of `κ.coord x` (Theorem 1.3.5 (preprint 1.25) for the affine coordinates
`v ↦ Ψ v + c`, which map `χ(s)` onto `W ∩ [0,∞)ⁿ`; corner charts realize `d_Q`). -/
theorem degIndex_eq_card {x : M} (hx : x ∈ κ.s) :
    Q.degIndex x = (Finset.univ.filter fun j => κ.coord x j = 0).card := by
  have himg := κ.image_s
  have hfU : MapsTo (fun v => κ.Ψ v + κ.c) (κ.χ '' κ.s) (κ.W ∩ {y | ∀ i, 0 ≤ y i}) := by
    rw [← himg]; exact mapsTo_image _ _
  have hgU : MapsTo (fun y => κ.Ψ.symm (y - κ.c)) (κ.W ∩ {y | ∀ i, 0 ≤ y i}) (κ.χ '' κ.s) := by
    intro y hy
    rw [← himg] at hy
    obtain ⟨v, hv, rfl⟩ := hy
    simpa using hv
  have hgf : ∀ v ∈ κ.χ '' κ.s, κ.Ψ.symm ((κ.Ψ v + κ.c) - κ.c) = v := fun v _ => by simp
  have hfg : ∀ y ∈ κ.W ∩ {y | ∀ i, 0 ≤ y i}, κ.Ψ (κ.Ψ.symm (y - κ.c)) + κ.c = y :=
    fun y _ => by simp
  rw [Q.degIndex_eq_chartDegIndex_of_isTameRetract κ.isChart κ.isCornerChart.isTameRetract
    (κ.s_subset hx), chartDegIndex,
    theorem_1_3_5 κ.isRelOpenInQuadrant_image_s (isRelOpenInQuadrant_stdQuadrant κ.isOpen_W)
      κ.isScSmooth_coordAff.isSc1 κ.isScSmooth_coordAffInv.isSc1 hfU hgU hgf hfg
      (mem_image_of_mem _ hx)]
  exact degIndex_stdQuadrant (κ.coord_nonneg hx)

/-- A point on the face `{yᵢ = 0}` of corner coordinates lies in `∂Q`. -/
theorem one_le_degIndex {x : M} (hx : x ∈ κ.s) {i : Fin n} (hi : κ.coord x i = 0) :
    1 ≤ Q.degIndex x := by
  rw [κ.degIndex_eq_card hx]
  exact Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩

/-- A point whose only vanishing coordinate is `yᵢ` has degeneracy index `1`. -/
theorem degIndex_eq_one {x : M} (hx : x ∈ κ.s) {i : Fin n} (hi : κ.coord x i = 0)
    (hj : ∀ j ≠ i, κ.coord x j ≠ 0) : Q.degIndex x = 1 := by
  rw [κ.degIndex_eq_card hx, Finset.card_eq_one]
  refine ⟨i, Finset.ext fun j => ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun h => by_contra fun hne => hj j hne h, fun h => h ▸ hi⟩

end CornerCoords

/-! ### The faces of a sub-M-polyfold with `d_S = d_X` lie in the faces of `X` -/

section Faces

open TameBoundary

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {S : Set X} [ParacompactSpace S] {hY : PX.IsSubMPolyfold S} {n : ℕ}

/-- The points of `ℝⁿ` near `y₀` on the face `{yᵢ = 0}` and on no other face. -/
private def faceCell (y₀ : Fin n → ℝ) (ε : ℝ) (i : Fin n) : Set (Fin n → ℝ) :=
  {y | y ∈ Metric.ball y₀ ε ∧ y i = 0 ∧ ∀ j ≠ i, 0 < y j}

private theorem convex_faceCell (y₀ : Fin n → ℝ) (ε : ℝ) (i : Fin n) :
    Convex ℝ (faceCell y₀ ε i) := by
  rintro y ⟨hyB, hyi, hyj⟩ z ⟨hzB, hzi, hzj⟩ a b ha hb hab
  refine ⟨convex_ball y₀ ε hyB hzB ha hb hab, ?_, fun j hj => ?_⟩
  · simp [hyi, hzi]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases ha.lt_or_eq with ha' | rfl
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' (hyj j hj)) (mul_nonneg hb (hzj j hj).le)
    · rw [zero_add] at hab; subst hab; simpa using hzj j hj

/-- A point of the closed face `{yᵢ = 0} ∩ [0,∞)ⁿ` near `y₀` is a limit of points of the open
face cell. -/
private theorem mem_closure_faceCell {y₀ y y' : Fin n → ℝ} {ε : ℝ} {i : Fin n}
    (hy : y ∈ Metric.ball y₀ ε) (hy0 : ∀ j, 0 ≤ y j) (hyi : y i = 0)
    (hy' : y' ∈ faceCell y₀ ε i) : y ∈ closure (faceCell y₀ ε i) := by
  refine closure_mono ?_ (segment_subset_closure_openSegment (left_mem_segment ℝ y y'))
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  refine ⟨(convex_ball y₀ ε).openSegment_subset hy hy'.1 ⟨a, b, ha, hb, hab, rfl⟩, ?_,
    fun j hj => ?_⟩
  · simp [hyi, hy'.2.1]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_pos_of_nonneg_of_pos (mul_nonneg ha.le (hy0 j)) (mul_pos hb (hy'.2.2 j hj))

namespace CornerCoords

/-- **The faces of `S` in its corner coordinates are cut out by the faces of `X`**: let `S` be a
sub-M-polyfold of a tame `X` with `d_S = d_X` on `S` (2021 Theorem 4.2.11 for a solution set in
general position, `theorem_6_6_18_solutionSet`), `κ` corner coordinates of `S` and `q₀` a point on
the face `{yᵢ = 0}` of `κ`.  There is an admissible boundary triple `t = (q₀, V, θ)` of `X`
(2021 Definition 2.7.10), with `V` centred at `q₀`, and an open `N ∋ q₀` of `S` in the piece of
`κ` such that every point of `N` on the face `{yᵢ = 0}` lies on the face `θ` of `V`.
*Proof*: near `κ(q₀)`, the points with `yᵢ = 0` and `y_j > 0` (`j ≠ i`) form a convex set of
points of `S` with `d_S = 1 = d_X` (`degIndex_eq_one`), so they lie in one component of
`{d_X = 1} ∩ V`; every point of the face near `κ(q₀)` is a limit of them. -/
theorem zero_coord_face (hX : PX.IsTame)
    (hdeg : ∀ a : S, (subPolyfold hY).degIndex a = PX.degIndex a)
    (κ : CornerCoords (subPolyfold hY) n) {q₀ : S} (hq₀ : q₀ ∈ κ.s) {i : Fin n}
    (hi : κ.coord q₀ i = 0) :
    ∃ t : BTriple (PX.isCornerIndex_degIndex hX), t.x = q₀.1 ∧
      IsCenteredAt PX.degIndex t.x t.V ∧
      ∃ N : Set S, IsOpen N ∧ q₀ ∈ N ∧ N ⊆ κ.s ∧
        ∀ q ∈ N, κ.coord q i = 0 → q.1 ∈ t.θ := by
  set hd := PX.isCornerIndex_degIndex hX
  set d := PX.degIndex
  have hd1 : 1 ≤ d q₀.1 := (hdeg q₀) ▸ κ.one_le_degIndex hq₀ hi
  obtain ⟨V₀, hV₀⟩ := faceStructuredNbhdsAt_nonempty hd q₀.1
  set V := reach d V₀ q₀.1 with hVdef
  have hV : V ∈ faceStructuredNbhdsAt d q₀.1 := reach_mem_faceStructuredNbhdsAt hd hV₀
  have hcent : IsCenteredAt d q₀.1 V := isCenteredAt_reach hd hV₀.1.1.1 hV₀.2.1
  have hVo : IsOpen V := hV.1.1.1
  -- a ball around `κ(q₀)` inside `W` whose quadrant part is mapped into `V`
  set N₀ : Set S := κ.s ∩ Subtype.val ⁻¹' V with hN₀
  have hN₀o : IsOpen N₀ := κ.isOpen_s.inter (hVo.preimage continuous_subtype_val)
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
  -- the open face cell and its points
  set G := faceCell y₀ ε i with hG
  have hGq : ∀ y ∈ G, y ∈ κ.W ∧ ∀ j, 0 ≤ y j := fun y hy =>
    ⟨hBW y hy.1, fun j => by
      by_cases hj : j = i
      · rw [hj, hy.2.1]
      · exact (hy.2.2 j hj).le⟩
  set y' : Fin n → ℝ := fun j => if j = i then 0 else y₀ j + ε / 2 with hy'
  have hy'G : y' ∈ G := by
    refine ⟨(dist_pi_lt_iff hε).2 fun j => ?_, by simp [hy'], fun j hj => ?_⟩
    · by_cases hj : j = i
      · subst hj; simp [hy', hi, hε]
      · simp only [hy', if_neg hj, Real.dist_eq, add_sub_cancel_left]
        rw [abs_of_pos (half_pos hε)]; exact half_lt_self hε
    · simp only [hy', if_neg hj]; linarith [hy₀q j]
  set K : Set X := Subtype.val '' (κ.coordInv '' G) with hK
  have hKpre : IsPreconnected K :=
    ((convex_faceCell y₀ ε i).isPreconnected.image _
      (κ.continuousOn_coordInv.mono fun y hy => hGq y hy)).image _
      continuous_subtype_val.continuousOn
  have hKsub : K ⊆ V ∩ {z | d z = 1} := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hyq := hGq y hy
    have hN := hBN y hy.1 hyq.2
    refine ⟨hN.2, ?_⟩
    change d (κ.coordInv y).1 = 1
    rw [← hdeg]
    refine κ.degIndex_eq_one hN.1 (i := i) ?_ fun j hj => ?_
    · rw [κ.coord_coordInv hyq.1 hyq.2]; exact hy.2.1
    · rw [κ.coord_coordInv hyq.1 hyq.2]; exact (hy.2.2 j hj).ne'
  set p : X := (κ.coordInv y').1 with hp
  have hpK : p ∈ K := ⟨_, ⟨y', hy'G, rfl⟩, rfl⟩
  have hcc : K ⊆ connectedComponentIn (V ∩ {z | d z = 1}) p :=
    hKpre.subset_connectedComponentIn hpK hKsub
  -- the neighbourhood `N` and the key inclusion
  set N : Set S := κ.s ∩ κ.coord ⁻¹' Metric.ball y₀ ε with hN
  have hNo : IsOpen N := κ.continuousOn_coord.isOpen_inter_preimage κ.isOpen_s Metric.isOpen_ball
  have hq₀N : q₀ ∈ N := ⟨hq₀, Metric.mem_ball_self hε⟩
  have key : ∀ q ∈ N, κ.coord q i = 0 → q.1 ∈ faceAt d V p := by
    intro q hqN hqi
    have hyB : κ.coord q ∈ Metric.ball y₀ ε := hqN.2
    have hy0 := κ.coord_nonneg hqN.1
    have hycl := mem_closure_faceCell hyB hy0 hqi hy'G
    have hcwq : ContinuousWithinAt κ.coordInv G (κ.coord q) :=
      (κ.continuousOn_coordInv _ ⟨hBW _ hyB, hy0⟩).mono fun y hy => hGq y hy
    have h1 := hcwq.mem_closure_image hycl
    rw [κ.coordInv_coord hqN.1] at h1
    have h2 : q.1 ∈ closure K :=
      continuous_subtype_val.continuousAt.continuousWithinAt.mem_closure_image h1
    have hqV : q.1 ∈ V := by
      have := hBN _ hyB hy0
      rw [κ.coordInv_coord hqN.1] at this
      exact this.2
    exact ⟨hqV, closure_mono hcc h2⟩
  have hpV : p ∈ V := (hKsub hpK).1
  have hp1 : d p = 1 := (hKsub hpK).2
  refine ⟨⟨⟨q₀.1, V, hV, hd1⟩, faceAt d V p, ⟨⟨p, hpV, hp1, rfl⟩, key q₀ hq₀N hi⟩⟩, rfl, hcent,
    N, hNo, hq₀N, fun _ hq => hq.1, key⟩

/-- **The lift to `bX`**: a point `q` of the face `θ` of a centred triple `t` has a unique lift
to `U(t) ⊆ bX` over it (`phi_bijective_of_isCenteredAt`, 2021 (2.44)). -/
theorem exists_lift_uSet (hX : PX.IsTame) {t : BTriple (PX.isCornerIndex_degIndex hX)}
    (ht : IsCenteredAt PX.degIndex t.x t.V) {q : X} (hq : q ∈ t.θ) :
    ∃! b, b ∈ uSet (PX.isCornerIndex_degIndex hX) t ∧
      bMap (PX.isCornerIndex_degIndex hX) b = q := by
  obtain ⟨⟨b, hb⟩, hbq⟩ := (phi_bijective_of_isCenteredAt (PX.isCornerIndex_degIndex hX) ht).2
    ⟨q, hq⟩
  refine ⟨b, ⟨hb, congrArg Subtype.val hbq⟩, fun b' hb' => ?_⟩
  exact bMap_injOn_uSet _ t hb'.1 hb (hb'.2.trans (congrArg Subtype.val hbq).symm)

/-- **Theorem 6.7.1 (2021, p. 277; preprint 6.43), the faces of `S_h`**: for a section `h` whose
solution set is in general position (`SolutionSetInGeneralPosition`, the conclusion of
Theorems 5.3.10 and 6.6.18), the faces of `S_h` in any corner coordinates lie, near each of their
points, in a face of a centred admissible triple of `X` (`zero_coord_face` with `d_S = d_X`). -/
theorem zero_coord_face_solutionSet {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [ParacompactSpace Y] {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    {B : StrongBundle PX P} {h : X → Y} (hX : PX.IsTame) (hgp : B.SolutionSetInGeneralPosition h)
    [ParacompactSpace (solutionSet P h)] {hY : PX.IsSubMPolyfold (solutionSet P h)}
    (κ : CornerCoords (subPolyfold hY) n) {q₀ : solutionSet P h} (hq₀ : q₀ ∈ κ.s) {i : Fin n}
    (hi : κ.coord q₀ i = 0) :
    ∃ t : BTriple (PX.isCornerIndex_degIndex hX), t.x = q₀.1 ∧
      IsCenteredAt PX.degIndex t.x t.V ∧
      ∃ N : Set (solutionSet P h), IsOpen N ∧ q₀ ∈ N ∧ N ⊆ κ.s ∧
        ∀ q ∈ N, κ.coord q i = 0 → q.1 ∈ t.θ := by
  obtain ⟨-, -, -, hS, -, hrest⟩ := hgp
  exact zero_coord_face hX hrest.2.2 κ hq₀ hi

end CornerCoords

end Faces

end MPolyfold

end Polyfold
