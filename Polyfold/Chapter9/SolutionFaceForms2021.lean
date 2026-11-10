import Polyfold.Chapter9.SolutionFaces2021
import Polyfold.Chapter7.Discrete

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, **Theorem 6.7.1**
(p. 277; preprint Theorem 6.43): the boundary term `∫_{∂S_{f+s}} τ` of `Ψ_{(f,o)}`, for a form
`τ ∈ Ω^*_∞(∂X)` of the relative complex of p. 198 (2017 p. 150; preprint p. 168).

# Forms on `∂X` restricted to the faces of a solution set

## The text, paraphrased

(p. 277) For `[ω, τ] ∈ H^*_dR(X, ∂X)` the invariant is `∫_{S} ω − ∫_{∂S} τ`, `S = S_{f+s}` a compact
manifold with boundary with corners whose faces lie in the faces of `X` (`SolutionFaces2021`).  The
form `τ` lives on `∂X` (read through the tame boundary `B : bX → X`, `BoundaryForms2021`), and
`∫_{∂S} τ` integrates its restriction to the faces of `S`.

## What is formalized

For a sub-M-polyfold `S ⊆ X` of a tame `X` with a corner structure of dimension `n + 1` and
`d_S = d_X` on `S` (the solution sets in general position, `theorem_6_6_18_oriented`):

* **`solFaceForm`**: `Ω^k_∞(∂X) →ₗ[ℝ] Ω^k(∂S)` (`ChartFaceForm S n k`, `ManifoldFaceForms2021`),
  `τ ↦ τ|_{∂S}`.  On the face `{yᵢ = 0}` of the corner chart at `x`, at the point `q` with face
  parameter `u` and for face vectors `w`, the value is `τ_b(β)`, where `b ∈ bX` lies over `q` and
  `TB βⱼ = Tι(wⱼ)` (`linLiftForm`, `solFaceFormData`); it does not depend on the lift `(b, β)`
  because `τ` agrees over `B` (`IsAgreeingOver`, the definition of `Ω^k(∂X)`).
* **`solFaceForm_isExtendedBy_jStar`**: `ω|_S` extends `(j^*ω)|_{∂S}`, so
  `∫_{∂S} (j^*ω)|_{∂S} = ∫_{∂S} ω|_S` (`solFaceForm_jStar_integral`, `ChartFaceForm.integral`).
* **`solFaceForm_d`**: `(dτ)|_{∂S} = d(τ|_{∂S})`.
* **`solFaceForm_corner`**: the corner condition, from the agreement over `B`.

## The route (chart by chart, no M-polyfold structure on the faces of `S`)

Near a face point `q₀` on the face `{yᵢ = 0}` of corner coordinates `κ` of `S`, the face parameters
`u` with `facePoint u` in the neighbourhood `N` of `zero_coord_face` form a relatively open piece
`U` of `[0,∞)ⁿ`.  It is a corner M-polyfold with one chart (`quadrantPiece`), the map
`e : U → S`, `u ↦ facePoint u` is sc-smooth (affine in the corner chart), its values lie in the
face `θ` of the triple `t` of `zero_coord_face`, and `g := Φ⁻¹ ∘ e : U → bX` is sc-smooth
(`phi_isScDiffeoOn`, Theorem 2.7.13).  The pull-back of `τ` along `g`, read as a Mathlib form on
`U` (`formsAlong`, `MathlibFormsBridge2021`), is `C^∞` and commutes with `d`; the key identity
`solFaceFormData_eq_chartForm` identifies it with `τ|_{∂S}` on `U`, through the tangent map of
`e` (`tangentMap_e_fiberMap`).  So the smoothness and `d` of `τ|_{∂S}` come from `formsAlong`,
and the chart-change and corner conditions from the agreement over `B`.

## The hypotheses

`hcs` (corner structure), `hch` (the charted space is `cornerChartedSpace hcs`) are those of
`MathlibFormsBridge2021`; `hX : PX.IsTame` as in the text; `hdeg : d_S = d_X` is Theorem 4.2.11
for the solution sets (`SolutionSetInGeneralPosition`, `zero_coord_face_solutionSet`).  No
hypothesis quantifies over charts.
-/

open Set Filter Topology Manifold Module WithLp
open scoped ContDiff

noncomputable section

namespace Polyfold

local notation "𝓠" => modelWithCornersEuclideanQuadrant

namespace MPolyfold

universe u v

/-! ### The value of a form on `bX` at lifted vectors -/

section LinLift

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {PY : MPolyfold Y}
  {Z : Type v} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}
  {B : Y → Z} {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A linear lift**: `b ∈ Y¹` over `y ∈ Z¹` and a linear map `L : E → T_bY` with
`TB ∘ L = V`. -/
structure IsLinLift (hB : PY.IsScSmoothMap PZ B) (y : PZ.Level 1) (V : E →ₗ[ℝ] PZ.tangentFiber y)
    (b : PY.Level 1) (L : E →ₗ[ℝ] PY.tangentFiber b) : Prop where
  base : B (PY.levelVal 1 b) = PZ.levelVal 1 y
  vec : ∀ w, tangentMap hB (L w).1 = (V w).1

open scoped Classical in
/-- **The value of `τ` at lifted vectors**: for a family `τ` of alternating forms on the tangent
spaces of `Y`, `y ∈ Z¹` and a linear `V : E → T_yZ`, the alternating form `w ↦ τ_b(L w₁, …, L w_k)`
for a linear lift `(b, L)` of `(y, V)` (`0` if there is none).  For `τ` agreeing over `B` it does
not depend on the lift (`linLiftForm_eq`). -/
def linLiftForm (hB : PY.IsScSmoothMap PZ B)
    (τ : ∀ b : PY.Level 1, PY.tangentFiber b [⋀^Fin k]→ₗ[ℝ] ℝ) (y : PZ.Level 1)
    (V : E →ₗ[ℝ] PZ.tangentFiber y) : E [⋀^Fin k]→ₗ[ℝ] ℝ :=
  if h : ∃ (b : PY.Level 1) (L : E →ₗ[ℝ] PY.tangentFiber b), IsLinLift hB y V b L then
    (τ h.choose).compLinearMap h.choose_spec.choose
  else 0

variable {hB : PY.IsScSmoothMap PZ B} {τ σ : ∀ b : PY.Level 1, PY.tangentFiber b [⋀^Fin k]→ₗ[ℝ] ℝ}
  {y : PZ.Level 1} {V : E →ₗ[ℝ] PZ.tangentFiber y}

/-- For `τ` agreeing over `B`, the value at any linear lift is `linLiftForm`. -/
theorem linLiftForm_eq (hτ : IsAgreeingOver hB τ) {b : PY.Level 1}
    {L : E →ₗ[ℝ] PY.tangentFiber b} (hl : IsLinLift hB y V b L) :
    linLiftForm hB τ y V = (τ b).compLinearMap L := by
  have h : ∃ (b : PY.Level 1) (L : E →ₗ[ℝ] PY.tangentFiber b), IsLinLift hB y V b L := ⟨b, L, hl⟩
  rw [linLiftForm, dif_pos h]
  ext w
  obtain ⟨hb, hβ⟩ := h.choose_spec.choose_spec
  exact hτ (hb.trans hl.base.symm) _ _ fun j => (hβ (w j)).trans (hl.vec (w j)).symm

theorem linLiftForm_add :
    linLiftForm hB (τ + σ) y V = linLiftForm hB τ y V + linLiftForm hB σ y V := by
  unfold linLiftForm
  split_ifs
  · rfl
  · simp

theorem linLiftForm_smul (c : ℝ) : linLiftForm hB (c • τ) y V = c • linLiftForm hB τ y V := by
  unfold linLiftForm
  split_ifs
  · rfl
  · simp

/-- `linLiftForm` of a pull-back `B^*ω` is `ω` itself at `(y, V)`, if a lift exists. -/
theorem linLiftForm_formPullback (η : ∀ z : PZ.Level 1, PZ.tangentFiber z [⋀^Fin k]→ₗ[ℝ] ℝ)
    {b : PY.Level 1} {L : E →ₗ[ℝ] PY.tangentFiber b} (hl : IsLinLift hB y V b L) :
    linLiftForm hB (formPullback hB η) y V = (η y).compLinearMap V := by
  rw [linLiftForm_eq (isAgreeingOver_formPullback hB η) hl]
  ext w
  change formPullback hB η b (fun j => L (w j)) = η y fun j => V (w j)
  rw [formPullback_apply]
  exact altFamily_congr η (level_ext (x := liftLevelOneMap hB b) hl.base) _ _ fun j => by
    rw [coe_tangentFiberMap_apply, hl.vec]

/-- Precomposition with a linear map, when a lift exists. -/
theorem linLiftForm_comp (hτ : IsAgreeingOver hB τ)
    (h : ∃ (b : PY.Level 1) (L : E →ₗ[ℝ] PY.tangentFiber b), IsLinLift hB y V b L)
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] (M : E' →ₗ[ℝ] E) :
    linLiftForm hB τ y (V ∘ₗ M) = (linLiftForm hB τ y V).compLinearMap M := by
  obtain ⟨b, L, hl⟩ := h
  rw [linLiftForm_eq hτ hl, linLiftForm_eq hτ (b := b) (L := L ∘ₗ M)
    ⟨hl.base, fun w => hl.vec (M w)⟩]
  rfl

/-- **Two lifted values agree** when the lifted linear maps have the same image under `TB`
(at the same base point). -/
theorem linLiftForm_apply_congr (hτ : IsAgreeingOver hB τ) {y y' : PZ.Level 1} (hyy' : y = y')
    {V : E →ₗ[ℝ] PZ.tangentFiber y} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {V' : E' →ₗ[ℝ] PZ.tangentFiber y'}
    (hV : ∃ (b : PY.Level 1) (L : E →ₗ[ℝ] PY.tangentFiber b), IsLinLift hB y V b L)
    (hV' : ∃ (b' : PY.Level 1) (L' : E' →ₗ[ℝ] PY.tangentFiber b'), IsLinLift hB y' V' b' L')
    (w : Fin k → E) (w' : Fin k → E') (hw : ∀ j, (V (w j)).1 = (V' (w' j)).1) :
    linLiftForm hB τ y V w = linLiftForm hB τ y' V' w' := by
  subst hyy'
  obtain ⟨b, L, hl⟩ := hV
  obtain ⟨b', L', hl'⟩ := hV'
  rw [linLiftForm_eq hτ hl, linLiftForm_eq hτ hl']
  exact hτ (hl.base.trans hl'.base.symm) _ _ fun j => by
    rw [hl.vec, hl'.vec, hw j]

end LinLift

/-! ### A relatively open piece of the quadrant `[0,∞)ⁿ ⊆ ℝⁿ` as a corner M-polyfold -/

section QuadrantPiece

variable {n : ℕ}

/-- The presentation `ℝⁿ ≅ ℝⁿ ⊕ ℝ⁰` of `EuclideanSpace ℝ (Fin n)` (constant sc-structures). -/
def euclidQuadrantPres (n : ℕ) :
    ScIso (ScBanach.const (EuclideanSpace ℝ (Fin n)))
      ((ScBanach.const (Fin n → ℝ)).prod (ScBanach.const (Fin 0 → ℝ))) where
  lvl _ := (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin n => ℝ).trans
    (ContinuousLinearEquiv.prodUnique ℝ (Fin n → ℝ) (Fin 0 → ℝ)).symm
  incl_comm _ _ := Prod.ext rfl (funext fun i => i.elim0)

theorem closedQuadrant_univ_eq (n : ℕ) : closedQuadrant (univ : Set (Fin n)) =
    (euclidQuadrantPres n) 0 ⁻¹' quadrant n (ScBanach.const (Fin 0 → ℝ)) 0 := by
  ext y
  exact ⟨fun h i => h i (mem_univ i), fun h i _ => h i⟩

/-- `[0,∞)ⁿ ⊆ EuclideanSpace ℝ (Fin n)` is a partial quadrant. -/
theorem isPartialQuadrant_closedQuadrant (n : ℕ) :
    IsPartialQuadrant (ScBanach.const (EuclideanSpace ℝ (Fin n))) (closedQuadrant univ) :=
  ⟨n, _, euclidQuadrantPres n, closedQuadrant_univ_eq n⟩

/-- `W ∩ [0,∞)ⁿ` is relatively open in the quadrant for open `W`. -/
theorem isRelOpenInQuadrant_inter_closedQuadrant {W : Set (EuclideanSpace ℝ (Fin n))}
    (hW : IsOpen W) :
    IsRelOpenInQuadrant (ScBanach.const (EuclideanSpace ℝ (Fin n))) (closedQuadrant univ)
      (W ∩ closedQuadrant univ) :=
  ⟨isPartialQuadrant_closedQuadrant n, W, hW, rfl⟩

variable {W : Set (EuclideanSpace ℝ (Fin n))} (hW : IsOpen W)
  (hne : (W ∩ closedQuadrant univ).Nonempty)

/-- The local model of the piece `W ∩ [0,∞)ⁿ` (the identity retraction). -/
abbrev quadrantPieceModel : LocalModel :=
  LocalModel.ofRelOpen (isRelOpenInQuadrant_inter_closedQuadrant hW)

/-- **The piece `W ∩ [0,∞)ⁿ` as an M-polyfold** with the single chart `id`. -/
abbrev quadrantPiece : MPolyfold ↥(W ∩ closedQuadrant univ) :=
  (quadrantPieceModel hW).toMPolyfold hne

/-- The chart `id` of the piece. -/
abbrev quadrantPieceChart : MChart ↥(W ∩ closedQuadrant univ) :=
  (quadrantPieceModel hW).selfChart hne

theorem quadrantPieceChart_isChart : (quadrantPiece hW hne).IsChart (quadrantPieceChart hW hne) :=
  (isRelOpenInQuadrant_inter_closedQuadrant hW).selfChart_isChart hne

theorem quadrantPieceChart_isCornerChart : (quadrantPieceChart hW hne).IsCornerChart :=
  ⟨EuclideanSpace ℝ (Fin n), inferInstance, inferInstance, inferInstance, closedQuadrant univ,
    W ∩ closedQuadrant univ, isRelOpenInQuadrant_inter_closedQuadrant hW, rfl⟩

open scoped Classical in
theorem quadrantPieceChart_symm_apply {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ W ∩ closedQuadrant univ) : (quadrantPieceChart hW hne).symm z = ⟨z, hz⟩ := by
  change (if h : z ∈ (quadrantPieceModel hW).O then (⟨z, h⟩ : (quadrantPieceModel hW).O) else _) = _
  exact dif_pos hz

/-- The piece has a corner structure of dimension `n`. -/
theorem quadrantPiece_hasCornerStructureOfDim :
    (quadrantPiece hW hne).HasCornerStructureOfDim n := fun u =>
  ⟨quadrantPieceChart hW hne, quadrantPieceChart_isChart hW hne, mem_univ u,
    quadrantPieceChart_isCornerChart hW hne, finrank_euclideanSpace_fin⟩

/-- **The standard corner coordinates of the piece**: the chart `id`, `Ψ = ofLp`, `c = 0`. -/
def quadrantPieceCoords : CornerCoords (quadrantPiece hW hne) n where
  χ := quadrantPieceChart hW hne
  isChart := quadrantPieceChart_isChart hW hne
  isCornerChart := quadrantPieceChart_isCornerChart hW hne
  s := univ
  isOpen_s := isOpen_univ
  s_subset := subset_univ _
  Ψ := PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin n => ℝ
  c := 0
  W := (toLp 2) ⁻¹' W
  isOpen_W := hW.preimage (PiLp.continuous_toLp 2 _)
  image_s := by
    have himg : quadrantPieceChart hW hne '' univ = W ∩ closedQuadrant univ :=
      (quadrantPieceChart hW hne).image_source
    rw [himg]
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨hvW, hvq⟩ : (v : EuclideanSpace ℝ (Fin n)) ∈ W ∧
        (v : EuclideanSpace ℝ (Fin n)) ∈ closedQuadrant univ := hv
      refine ⟨?_, fun i => ?_⟩
      · change toLp 2 (ofLp (v : EuclideanSpace ℝ (Fin n)) + 0) ∈ W
        rw [add_zero]
        exact hvW
      · change 0 ≤ (ofLp (v : EuclideanSpace ℝ (Fin n)) + 0) i
        rw [add_zero]
        exact hvq i (mem_univ i)
    · rintro ⟨hyW, hy⟩
      refine ⟨toLp 2 y, ⟨hyW, fun i _ => hy i⟩, ?_⟩
      change ofLp (toLp 2 y) + 0 = y
      simp

theorem quadrantPieceCoords_lin (w : EuclideanSpace ℝ (Fin n)) :
    (quadrantPieceCoords hW hne).lin w = w := rfl

theorem quadrantPieceCoords_coord (u : ↥(W ∩ closedQuadrant univ)) :
    (quadrantPieceCoords hW hne).coord u = ofLp u.1 := by
  change ofLp u.1 + 0 = _
  simp

/-- The target of the Mathlib chart of the piece is the piece. -/
theorem quadrantPieceCoords_extend_target :
    ((quadrantPieceCoords hW hne).toQuadrantChart.extend (𝓠 n)).target =
      W ∩ closedQuadrant univ := by
  ext y
  rw [OpenPartialHomeomorph.extend_target, range_modelWithCornersEuclideanQuadrant]
  constructor
  · rintro ⟨hy1, hy2⟩
    refine ⟨?_, hy2⟩
    have h := (quadrantPieceCoords hW hne).mem_toQuadrantChart_target.1 hy1
    change toLp 2 (ofLp ((𝓠 n).symm y).1) ∈ W at h
    rwa [toLp_ofLp, show ((𝓠 n).symm y).1 = y from
      CornerCoords.quadrant_right_inv fun i => hy2 i (mem_univ i)] at h
  · rintro ⟨hyW, hyq⟩
    refine ⟨?_, hyq⟩
    change toLp 2 (ofLp ((𝓠 n).symm y).1) ∈ W
    rwa [toLp_ofLp, show ((𝓠 n).symm y).1 = y from
      CornerCoords.quadrant_right_inv fun i => hyq i (mem_univ i)]

theorem quadrantPieceCoords_extend_symm {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ W ∩ closedQuadrant univ) :
    ((quadrantPieceCoords hW hne).toQuadrantChart.extend (𝓠 n)).symm y = ⟨y, hy⟩ := by
  rw [(quadrantPieceCoords hW hne).extend_symm_eq_coordInv
    (by rw [range_modelWithCornersEuclideanQuadrant]; exact hy.2)]
  change (quadrantPieceChart hW hne).symm ((PiLp.continuousLinearEquiv 2 ℝ _).symm (ofLp y - 0)) = _
  rw [sub_zero]
  exact quadrantPieceChart_symm_apply hW hne hy

theorem quadrantPieceCoords_extend_apply (u : ↥(W ∩ closedQuadrant univ)) :
    (quadrantPieceCoords hW hne).toQuadrantChart.extend (𝓠 n) u = u.1 := by
  rw [(quadrantPieceCoords hW hne).extend_eq_toLp_coord (mem_univ u), quadrantPieceCoords_coord]

end QuadrantPiece

/-! ### A map into a sub-M-polyfold -/

section CodRestrict

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

/-- Two `ScMap`s with the same values are equal. -/
theorem _root_.Polyfold.ScMap.ext_fun {f g : ScMap P Q} (h : ∀ x, f x = g x) : f = g := by
  cases f
  cases g
  congr
  funext x
  exact h x

/-- **A map into a sub-M-polyfold** `A ⊆ Y` is sc-smooth into `A` as soon as it is sc-smooth
into `Y` (Proposition 2.3.19 (2): near `x`, `f = (i⁻¹ ∘ r) ∘ i ∘ f` for a retraction `r` onto `A`;
the same argument as the private lemma of `Chapter7/SubGroupoid`). -/
theorem isScSmoothOn_subPolyfold_of_val {A : Set Y} (hA : Q.IsSubMPolyfold A)
    [ParacompactSpace A] {f : X → A} {U : Set X}
    (hf : P.IsScSmoothOn Q (fun x => (f x : Y)) U) :
    P.IsScSmoothOn (subPolyfold hA) f U := by
  refine IsScSmoothOn.of_locally hf.isOpen fun x hx => ?_
  set d := hA.data (f x).2
  have hU' : IsOpen (U ∩ (fun x => (f x : Y)) ⁻¹' d.V) :=
    hf.continuousOn.isOpen_inter_preimage hf.isOpen d.isOpen
  refine ⟨_, hU', ⟨hx, hA.mem_data_V (f x).2⟩, inter_subset_left, ?_⟩
  refine (IsScSmoothOn.comp (subPolyfold_retraction_isScSmooth hA d (f x))
    (hf.mono hU' inter_subset_left) fun y hy => hy.2).congr fun y hy => Subtype.ext ?_
  simp only [Function.comp_apply]
  rw [d.retractInto_val (f x) hy.2]
  exact d.apply_eq_self ⟨(f y).2, hy.2⟩

end CodRestrict

/-! ### Generic helpers on corner M-polyfolds -/

section Generic

universe w

variable {M : Type u} [TopologicalSpace M] [T2Space M] [ParacompactSpace M] {Q : MPolyfold M}
  {n : ℕ}

/-- The vector `κ.fiberMap v` at equal points. -/
theorem CornerCoords.coe_fiberMap_congr (κ : CornerCoords Q n) {x x' : Q.Level 1} (h : x = x')
    (hx : Q.levelVal 1 x ∈ κ.χ.source) (hx' : Q.levelVal 1 x' ∈ κ.χ.source)
    (v : EuclideanSpace ℝ (Fin n)) : (κ.fiberMap hx v).1 = (κ.fiberMap hx' v).1 := by
  subst h; rfl

/-- **The index raises are natural in the source**: `(f ∘ e)^m = f^m ∘ e` for a map `e` between
corner M-polyfolds. -/
theorem alongLift_comp {M' : Type w} [TopologicalSpace M'] [T2Space M'] [ParacompactSpace M']
    {Q' : MPolyfold M'} {n' : ℕ} (hcs : Q.HasCornerStructureOfDim n)
    (hcs' : Q'.HasCornerStructureOfDim n') {A : BundledMPolyfold.{v}} (f : ScMap Q' A.P)
    (e : ScMap Q Q') : ∀ (m : ℕ) (u : M), alongLift hcs (f.comp e) m u = alongLift hcs' f m (e u)
  | 0, _ => rfl
  | m + 1, u => level_ext (alongLift_comp hcs hcs' f e m u)

variable (hcs : Q.HasCornerStructureOfDim n) [inst : ChartedSpace (EuclideanQuadrant n) M]
  (hch : inst = Q.cornerChartedSpace hcs)
include hch

/-- **`cornerForm η` in the Mathlib chart of corner coordinates `κ`, on the vectors
`κ.fiberMap w`** (the first half of `chartForm_cornerForm`). -/
theorem chartForm_cornerForm_fiberMap (κ : CornerCoords Q n) {k : ℕ}
    (η : ∀ x : Q.Level 1, Q.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ (κ.toQuadrantChart.extend (𝓠 n)).target) (w : Fin k → EuclideanSpace ℝ (Fin n)) :
    ManifoldForm.chartForm (𝓠 n) κ.toQuadrantChart (cornerForm hcs η) y w =
      η (hcs.levelOne ((κ.toQuadrantChart.extend (𝓠 n)).symm y)) fun j =>
        κ.fiberMap (x := hcs.levelOne _) (κ.s_subset (κ.symm_mem_and_aff_eq hy).1) (w j) := by
  obtain ⟨hx', -⟩ := κ.symm_mem_and_aff_eq hy
  set x' := (κ.toQuadrantChart.extend (𝓠 n)).symm y
  change η (hcs.levelOne x') (fun i => (hcs.coords x').fiberMap (hcs.levelOne_mem_coords x')
    (chartChangeDeriv (𝓠 n) κ.toQuadrantChart (chartAt (EuclideanQuadrant n) x') x' (w i))) = _
  rw [chartAt_eq_of_eq hcs hch x']
  congr 1
  funext j
  exact fiberMap_chartChange hch κ (hcs.coords x') hx' (hcs.mem_coords x') (w j)

end Generic

/-! ### The local data at a face point of `S` -/

section SolFace

open TameBoundary BundledMPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {S : Set X} [ParacompactSpace S] {hY : PX.IsSubMPolyfold S} {n : ℕ}
  (hcs : (subPolyfold hY).HasCornerStructureOfDim (n + 1))

/-- **The local data at a face point** (`CornerCoords.zero_coord_face`): an admissible boundary
triple `t = (q₀, V, θ)` of `X` with `V` centred, and an open `N ∋ q₀` of `S` in the piece of the
corner coordinates `hcs.coords x`, whose points on the face `{yᵢ = 0}` lie on the face `θ`; with a
base face parameter `u₀` over `N`. -/
structure FaceLiftData (hX : PX.IsTame) (x : S) (i : Fin (n + 1)) where
  /-- The admissible boundary triple. -/
  t : BTriple (PX.isCornerIndex_degIndex hX)
  centred : IsCenteredAt PX.degIndex t.x t.V
  /-- The open neighbourhood in `S`. -/
  N : Set S
  isOpen_N : IsOpen N
  N_subset : N ⊆ (hcs.coords x).s
  face : ∀ q ∈ N, (hcs.coords x).coord q i = 0 → q.1 ∈ t.θ
  /-- The base face parameter. -/
  u₀ : EuclideanSpace ℝ (Fin n)
  u₀_mem : u₀ ∈ faceDomain (hcs.coords x).toQuadrantChart i
  facePoint_u₀_mem : facePoint (hcs.coords x).toQuadrantChart i u₀ ∈ N

variable {hcs}

/-- A point on the face `{yᵢ = 0}` of the chart has `i`-th coordinate `0`. -/
theorem CornerCoords.coord_facePoint_eq_zero (κ : CornerCoords (subPolyfold hY) (n + 1))
    {i : Fin (n + 1)} {u : EuclideanSpace ℝ (Fin n)} (hu : u ∈ faceDomain κ.toQuadrantChart i) :
    κ.coord (facePoint κ.toQuadrantChart i u) i = 0 := by
  have h1 := κ.extend_eq_toLp_coord (facePoint_mem_source hu)
  rw [extend_facePoint hu] at h1
  have h2 := congrArg (fun y : EuclideanSpace ℝ (Fin (n + 1)) => y i) h1
  simpa using h2.symm

/-- A face point lies in the piece `s` of the corner coordinates. -/
theorem CornerCoords.facePoint_mem_s (κ : CornerCoords (subPolyfold hY) (n + 1))
    {i : Fin (n + 1)} {u : EuclideanSpace ℝ (Fin n)} (hu : u ∈ faceDomain κ.toQuadrantChart i) :
    facePoint κ.toQuadrantChart i u ∈ κ.s :=
  facePoint_mem_source hu

/-- **The local data exist** at every face point, for a tame `X` and `d_S = d_X`
(`CornerCoords.zero_coord_face`). -/
theorem exists_faceLiftData (hX : PX.IsTame)
    (hdeg : ∀ a : S, (subPolyfold hY).degIndex a = PX.degIndex a) (x : S) (i : Fin (n + 1))
    {u₀ : EuclideanSpace ℝ (Fin n)} (hu₀ : u₀ ∈ faceDomain (hcs.coords x).toQuadrantChart i) :
    ∃ D : FaceLiftData hcs hX x i, D.u₀ = u₀ := by
  obtain ⟨t, -, ht, N, hNo, hq₀N, hNs, hface⟩ := CornerCoords.zero_coord_face hX hdeg
    (hcs.coords x) (facePoint_mem_source hu₀) ((hcs.coords x).coord_facePoint_eq_zero hu₀)
  exact ⟨⟨t, ht, N, hNo, hNs, hface, u₀, hu₀, hq₀N⟩, rfl⟩

namespace FaceLiftData

variable {hX : PX.IsTame} {x : S} {i : Fin (n + 1)} (D : FaceLiftData hcs hX x i)

/-- The open set of face parameters whose face point lies in `N`. -/
def W₀ : Set (EuclideanSpace ℝ (Fin n)) :=
  faceEmbedding i ⁻¹' ((𝓠 (n + 1)).symm ⁻¹' ((hcs.coords x).toQuadrantChart.target ∩
    (hcs.coords x).toQuadrantChart.symm ⁻¹' D.N))

theorem isOpen_W₀ : IsOpen D.W₀ :=
  (((hcs.coords x).toQuadrantChart.isOpen_inter_preimage_symm D.isOpen_N).preimage
    (𝓠 (n + 1)).continuous_symm).preimage (faceEmbedding i).continuous

/-- **The face parameter piece** `U = W₀ ∩ [0,∞)ⁿ`: the face parameters over `N`. -/
abbrev U : Set (EuclideanSpace ℝ (Fin n)) := D.W₀ ∩ closedQuadrant univ

theorem mem_U_iff {u : EuclideanSpace ℝ (Fin n)} :
    u ∈ D.U ↔ u ∈ faceDomain (hcs.coords x).toQuadrantChart i ∧
      facePoint (hcs.coords x).toQuadrantChart i u ∈ D.N := by
  rw [faceDomain_eq, facePoint, OpenPartialHomeomorph.extend_coe_symm]
  simp only [U, W₀, mem_inter_iff, mem_preimage, Function.comp_apply]
  tauto

theorem U_subset_faceDomain : D.U ⊆ faceDomain (hcs.coords x).toQuadrantChart i :=
  fun _ hu => (D.mem_U_iff.1 hu).1

theorem facePoint_mem_N {u : EuclideanSpace ℝ (Fin n)} (hu : u ∈ D.U) :
    facePoint (hcs.coords x).toQuadrantChart i u ∈ D.N := (D.mem_U_iff.1 hu).2

theorem nonempty_U : D.U.Nonempty := ⟨D.u₀, D.mem_U_iff.2 ⟨D.u₀_mem, D.facePoint_u₀_mem⟩⟩

theorem W₀_inter_faceDomain : D.W₀ ∩ faceDomain (hcs.coords x).toQuadrantChart i = D.U := by
  ext u
  simp only [U, W₀, faceDomain_eq, mem_inter_iff, mem_preimage]
  tauto

/-- `U` is a neighbourhood of each of its points within the face domain. -/
theorem U_mem_nhdsWithin {u : EuclideanSpace ℝ (Fin n)} (hu : u ∈ D.U) :
    D.U ∈ 𝓝[faceDomain (hcs.coords x).toQuadrantChart i] u := by
  rw [← D.W₀_inter_faceDomain]
  exact Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (D.isOpen_W₀.mem_nhds hu.1))
    self_mem_nhdsWithin

/-- `U` and the face domain agree near each point of `U`. -/
theorem U_eventuallyEq_faceDomain {u : EuclideanSpace ℝ (Fin n)} (hu : u ∈ D.U) :
    D.U =ᶠ[𝓝 u] faceDomain (hcs.coords x).toQuadrantChart i := by
  rw [Filter.eventuallyEq_set]
  filter_upwards [D.isOpen_W₀.mem_nhds hu.1] with z hz
  rw [← D.W₀_inter_faceDomain]
  exact and_iff_right hz

/-- The piece `U` as a corner M-polyfold (one chart). -/
abbrev Q : MPolyfold ↥D.U := quadrantPiece D.isOpen_W₀ D.nonempty_U

/-- Its corner structure of dimension `n`. -/
abbrev hcsQ : D.Q.HasCornerStructureOfDim n :=
  quadrantPiece_hasCornerStructureOfDim D.isOpen_W₀ D.nonempty_U

/-- Its standard corner coordinates. -/
abbrev κQ : CornerCoords D.Q n := quadrantPieceCoords D.isOpen_W₀ D.nonempty_U

/-- **The face map `e : U → S`**, `u ↦ facePoint u`. -/
def e (u : D.U) : S := facePoint (hcs.coords x).toQuadrantChart i u.1

theorem e_mem_N (u : D.U) : D.e u ∈ D.N := D.facePoint_mem_N u.2

theorem e_mem_s (u : D.U) : D.e u ∈ (hcs.coords x).s := D.N_subset (D.e_mem_N u)

theorem coord_e (u : D.U) : (hcs.coords x).coord (D.e u) i = 0 :=
  (hcs.coords x).coord_facePoint_eq_zero (D.U_subset_faceDomain u.2)

/-- The face points lie on the face `θ` of `X`. -/
theorem e_mem_θ (u : D.U) : (D.e u).1 ∈ D.t.θ := D.face _ (D.e_mem_N u) (D.coord_e u)

theorem faceEmbedding_mem_range (u : D.U) : faceEmbedding i u.1 ∈ range (𝓠 (n + 1)) :=
  (hcs.coords x).toQuadrantChart.extend_target_subset_range (D.U_subset_faceDomain u.2)

theorem e_eq_coordInv (u : D.U) :
    D.e u = (hcs.coords x).coordInv (ofLp (faceEmbedding i u.1)) :=
  (hcs.coords x).extend_symm_eq_coordInv (D.faceEmbedding_mem_range u)

theorem continuous_e : Continuous D.e :=
  (continuousOn_facePoint _ i).comp_continuous continuous_subtype_val fun u =>
    D.U_subset_faceDomain u.2

/-- The affine expression `z ↦ Ψ⁻¹(ιᵢ z − c)` of `e` in the corner charts. -/
def eAff (_D : FaceLiftData hcs hX x i) (z : EuclideanSpace ℝ (Fin n)) :
    (hcs.coords x).χ.model.E 0 :=
  (hcs.coords x).Ψ.symm (ofLp (faceEmbedding i z) - (hcs.coords x).c)

theorem contDiff_eAff : ContDiff ℝ ∞ D.eAff :=
  (hcs.coords x).Ψ.symm.contDiff.comp
    ((PiLp.contDiff_ofLp.comp (faceEmbedding i).contDiff).sub contDiff_const)

/-- The derivative of the affine expression: `Ψ⁻¹ ∘ ιᵢ`. -/
abbrev eDeriv (_D : FaceLiftData hcs hX x i) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] (hcs.coords x).χ.model.E 0 :=
  (hcs.coords x).Ψ.symm.toContinuousLinearMap.comp ((ofLpCLM (n + 1)).comp (faceEmbedding i))

theorem hasFDerivAt_eAff (z : EuclideanSpace ℝ (Fin n)) : HasFDerivAt D.eAff D.eDeriv z :=
  (hcs.coords x).Ψ.symm.hasFDerivAt.comp z
    (((ofLpCLM (n + 1)).hasFDerivAt.comp z (faceEmbedding i).hasFDerivAt).sub_const _)

theorem chart_e (u : D.U) : (hcs.coords x).χ (D.e u) = D.eAff u.1 := by
  obtain ⟨hyW, hy0⟩ :=
    (hcs.coords x).coord_mem_of_mem_extend_target (D.U_subset_faceDomain u.2)
  rw [D.e_eq_coordInv]
  exact (hcs.coords x).apply_coordInv hyW hy0

/-- The local expression of `e` in the chart `id` of `U` and the corner chart of `S`. -/
theorem chart_e_symm {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ D.U) :
    (hcs.coords x).χ (D.e ((quadrantPieceChart D.isOpen_W₀ D.nonempty_U).symm z)) = D.eAff z := by
  rw [quadrantPieceChart_symm_apply _ _ hz, D.chart_e]

/-- **`e : U → S` is sc-smooth** (affine in the corner charts). -/
theorem isScSmoothMap_e : D.Q.IsScSmoothMap (subPolyfold hY) D.e := by
  refine IsScSmoothOn.of_exists_charts isOpen_univ D.continuous_e.continuousOn fun u _ => ?_
  refine ⟨quadrantPieceChart D.isOpen_W₀ D.nonempty_U, (hcs.coords x).χ, univ,
    quadrantPieceChart_isChart _ _, (hcs.coords x).isChart, isOpen_univ, mem_univ _,
    fun _ _ => ⟨mem_univ _, mem_univ _⟩, fun u _ => (hcs.coords x).s_subset (D.e_mem_s u), ?_⟩
  have himg : quadrantPieceChart D.isOpen_W₀ D.nonempty_U '' univ = D.U :=
    (quadrantPieceChart _ _).image_source
  rw [himg]
  have := (hcs.coords x).isCornerChart.finiteDimensional
  have hU := isRelOpenInQuadrant_inter_closedQuadrant (n := n) D.isOpen_W₀
  refine (isScSmoothRetractMap_iff_exists hU.isScRetract).2
    ⟨fun z hz => ?_, ScRetraction.id hU, image_id _, ?_⟩
  · change (hcs.coords x).χ (D.e ((quadrantPieceChart _ _).symm z)) ∈ _
    rw [quadrantPieceChart_symm_apply _ _ hz]
    exact (hcs.coords x).χ.mapsTo_model _ ((hcs.coords x).s_subset (D.e_mem_s _))
  · refine (isScSmooth_of_contDiffOn_const_finiteDim hU.isScDomain
      D.contDiff_eAff.contDiffOn).congr hU.isScDomain fun z hz => ?_
    exact (D.chart_e_symm hz).symm

/-- `e` as an `ScMap`. -/
def eMap : ScMap D.Q (subPolyfold hY) := ⟨D.e, D.isScSmoothMap_e⟩

/-- **The lift `g : U → bX`** of the face map through `Φ_{(q₀,V,θ)}⁻¹ : θ → U(q₀, V, θ) ⊆ bX`. -/
def g (u : D.U) : PX.TameBoundarySpace hX :=
  ((phiHomeomorph _ D.centred).symm ⟨(D.e u).1, D.e_mem_θ u⟩ : PX.TameBoundarySpace hX)

theorem tameBoundaryMap_g (u : D.U) : PX.tameBoundaryMap hX (D.g u) = (D.e u).1 :=
  bMap_phiHomeomorph_symm _ _

/-- **`g : U → bX` is sc-smooth**: `e` is sc-smooth into the face `θ` (a sub-M-polyfold of `X`),
and `Φ⁻¹` is sc-smooth (Theorem 2.7.13, `phi_isScDiffeoOn`). -/
theorem isScSmoothMap_g : D.Q.IsScSmoothMap (PX.tameBoundaryPolyfold hX) D.g := by
  let _ := PX.paracompactSpace_subtype D.t.θ
  have h1 : D.Q.IsScSmoothMap (PX.facePolyfold hX D.t.mem.1.1 D.t.mem_faces.1)
      (fun u => (⟨(D.e u).1, D.e_mem_θ u⟩ : D.t.θ)) :=
    isScSmoothOn_subPolyfold_of_val _
      ((subPolyfold_inclusion_isScSmooth hY).comp D.isScSmoothMap_e)
  exact (PX.phi_isScDiffeoOn hX D.t D.centred).isScSmoothOn_inv.comp h1 (mapsTo_univ _ _)

/-- `g` as an `ScMap` into `bX`. -/
def gMap : ScMap D.Q (bdry hX).P := ⟨D.g, D.isScSmoothMap_g⟩

/-- `B ∘ g = ι ∘ e`. -/
theorem bdryMap_comp_gMap : (bdryMap hX).comp D.gMap = (subInclScMap hY).comp D.eMap :=
  ScMap.ext_fun fun u => D.tameBoundaryMap_g u

/-! ### The tangent map of the face map `e` -/

/-- The local expression of `e` is sc-smooth between the retracts. -/
theorem isScSmoothRetractMap_e :
    IsScSmoothRetractMap (ScBanach.const (EuclideanSpace ℝ (Fin n))) (closedQuadrant univ) D.U
      (hcs.coords x).χ.model.E (hcs.coords x).χ.model.C (hcs.coords x).χ.model.O
      ((hcs.coords x).χ ∘ D.e ∘ (quadrantPieceChart D.isOpen_W₀ D.nonempty_U).symm) := by
  have h := D.isScSmoothMap_e.smooth (quadrantPieceChart D.isOpen_W₀ D.nonempty_U)
    (hcs.coords x).χ (quadrantPieceChart_isChart _ _) (hcs.coords x).isChart univ isOpen_univ
    (fun _ _ => ⟨mem_univ _, mem_univ _⟩) fun u _ => (hcs.coords x).s_subset (D.e_mem_s u)
  have himg : quadrantPieceChart D.isOpen_W₀ D.nonempty_U '' univ = D.U :=
    (quadrantPieceChart _ _).image_source
  rwa [himg] at h

theorem uniqueDiffOn_U : UniqueDiffOn ℝ D.U := by
  rw [show D.U = closedQuadrant univ ∩ D.W₀ from inter_comm _ _]
  exact uniqueDiffOn_quadrant.inter D.isOpen_W₀

/-- `u ∈ U` lies on level `1` of the piece. -/
theorem mem_levelSet_one (u : D.U) : u ∈ D.Q.levelSet 1 :=
  mem_iInter.1 (D.hcsQ.mem_smoothSet u) 1

/-- **The tangent map of `e` on the corner frames**: `Te(κ_U.fiberMap w) = κ.fiberMap (ιᵢ w)`,
by `tangentChartMap_tangentMap` and the derivative `Ψ⁻¹ ∘ ιᵢ` of the affine expression of `e`. -/
theorem tangentMap_e_fiberMap (u : D.U) (w : EuclideanSpace ℝ (Fin n)) :
    tangentMap D.isScSmoothMap_e
        (D.κQ.fiberMap (x := D.hcsQ.levelOne u) (D.κQ.s_subset (mem_univ _)) w).1 =
      ((hcs.coords x).fiberMap (x := hcs.levelOne (D.e u))
        ((hcs.coords x).s_subset (D.e_mem_s u)) (faceEmbedding i w)).1 := by
  set κ := hcs.coords x
  set φQ := quadrantPieceChart D.isOpen_W₀ D.nonempty_U
  have hφQ : D.Q.IsChart φQ := quadrantPieceChart_isChart _ _
  set α := (D.κQ.fiberMap (x := D.hcsQ.levelOne u) (D.κQ.s_subset (mem_univ _)) w).1
  have hαf : α ∈ D.Q.tangentFiber (D.hcsQ.levelOne u) := (D.κQ.fiberMap _ w).2
  have hα : α ∈ tangentChartSet φQ := mem_tangentChartSet_of_mem_fiber (mem_univ _) hαf
  have hproj : D.Q.tangentProj α = D.hcsQ.levelOne u := hαf
  have hfα : D.e (D.Q.levelVal 1 (D.Q.tangentProj α)) ∈ κ.χ.source := by
    rw [hproj]; exact κ.s_subset (D.e_mem_s u)
  have hL : tangentMap D.isScSmoothMap_e α ∈ (subPolyfold hY).tangentFiber (hcs.levelOne (D.e u)) :=
    tangentMap_mapsTo_fiber D.isScSmoothMap_e (D.hcsQ.levelOne u) (hcs.levelOne (D.e u)) rfl hαf
  have hes : (subPolyfold hY).levelVal 1 (hcs.levelOne (D.e u)) ∈ κ.χ.source :=
    κ.s_subset (D.e_mem_s u)
  refine tangentChartMap_injOn κ.isChart (mem_tangentChartSet_of_mem_fiber hes hL)
    (mem_tangentChartSet_of_mem_fiber hes (κ.fiberMap hes (faceEmbedding i w)).2) ?_
  refine Prod.ext ?_ ?_
  · rw [tangentChartMap_fst_of_mem_fiber κ.isChart hes hL,
      tangentChartMap_fst_of_mem_fiber κ.isChart hes (κ.fiberMap hes (faceEmbedding i w)).2]
  rw [κ.tangentChartMap_fiberMap, tangentChartMap_tangentMap D.isScSmoothMap_e hφQ κ.isChart hα hfα]
  have hfd : TangentPre.fdom φQ D.e κ.χ = univ :=
    eq_univ_of_forall fun u => ⟨mem_univ _, κ.s_subset (D.e_mem_s u)⟩
  have himg : φQ '' univ = D.U := φQ.image_source
  rw [hfd, himg]
  have hU := isRelOpenInQuadrant_inter_closedQuadrant (n := n) D.isOpen_W₀
  have hp : tangentChartMap hφQ α ∈ retractTangent φQ.model.E φQ.model.C D.U :=
    tangentChartMap_mem hφQ hα
  have hr : (retractTangentMap φQ.model.E φQ.model.C D.U (κ.χ ∘ D.e ∘ φQ.symm)
      (tangentChartMap hφQ α)).2 = scDeriv D.U ((κ.χ ∘ D.e ∘ φQ.symm) ∘ ScRetraction.id hU)
        (tangentChartMap hφQ α).1 (tangentChartMap hφQ α).2 :=
    congrArg Prod.snd
      (retractTangentMap_apply D.isScSmoothRetractMap_e (ScRetraction.id hU) (image_id _) hp)
  rw [hr]
  have h2 : (tangentChartMap hφQ α).2 = w :=
    D.κQ.tangentChartMap_fiberMap (D.κQ.s_subset (mem_univ _)) w
  have h1 : (tangentChartMap hφQ α).1 = levelLift φQ 1 u :=
    tangentChartMap_fst_of_mem_fiber hφQ (mem_univ _) hαf
  have hbase : (ScBanach.const (EuclideanSpace ℝ (Fin n))).toBase 1 (tangentChartMap hφQ α).1 =
      u.1 := by
    rw [h1]
    exact D.Q.toBase_levelLift hφQ (mem_univ _) (D.mem_levelSet_one u)
  have hfin : FiniteDimensional ℝ ((ScBanach.const (EuclideanSpace ℝ (Fin n))) 0) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n)))
  have hsc : IsSc1 D.U ((κ.χ ∘ D.e ∘ φQ.symm) ∘ ScRetraction.id hU) :=
    (D.isScSmoothRetractMap_e.comp_isScSmooth (ScRetraction.id hU) (image_id _)).isSc1
  have hD := hsc.hasFDerivWithinAt_of_finiteDimensional (x := (tangentChartMap hφQ α).1)
    (by rw [hbase]; exact u.2)
  rw [hbase] at hD
  have hE : HasFDerivWithinAt ((κ.χ ∘ D.e ∘ φQ.symm) ∘ ScRetraction.id hU) D.eDeriv D.U u.1 :=
    (D.hasFDerivAt_eAff u.1).hasFDerivWithinAt.congr (fun z hz => D.chart_e_symm hz)
      (D.chart_e_symm u.2)
  rw [(D.uniqueDiffOn_U u.1 u.2).eq hD hE, h2]
  rfl

end FaceLiftData

/-! ### The restriction of forms on `∂X` to the faces of `S` -/

variable (hcs) (hX : PX.IsTame)

/-- The inclusion `ι^m : S → X^m` (`alongLift`). -/
abbrev solIncl (m : ℕ) : ScMap (subPolyfold hY) ((BundledMPolyfold.of PX).lift m).P :=
  alongLift hcs (subInclScMap hY) m

/-- The point `ι^m q ∈ (X^m)¹` over `q ∈ S`. -/
abbrev solPt (m : ℕ) (q : S) : ((BundledMPolyfold.of PX).lift m).P.Level 1 :=
  liftLevelOneMap (solIncl hcs m).isScSmoothMap (hcs.levelOne q)

/-- **The face vectors in `TX^m`**: `v ↦ Tι^m(κ.fiberMap v)` at `q`, linear in `v ∈ ℝⁿ⁺¹`. -/
def solVec (m : ℕ) (κ : CornerCoords (subPolyfold hY) (n + 1)) {q : S} (hq : q ∈ κ.s) :
    EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ((BundledMPolyfold.of PX).lift m).P.tangentFiber
      (solPt hcs m q) :=
  (tangentFiberMap (solIncl hcs m).isScSmoothMap (hcs.levelOne q) :
    _ →ₗ[ℝ] _) ∘ₗ κ.fiberMap (x := hcs.levelOne q) (κ.s_subset hq)

theorem coe_solVec (m : ℕ) (κ : CornerCoords (subPolyfold hY) (n + 1)) {q : S} (hq : q ∈ κ.s)
    (v : EuclideanSpace ℝ (Fin (n + 1))) :
    (solVec hcs m κ hq v).1 = tangentMap (solIncl hcs m).isScSmoothMap
      (κ.fiberMap (x := hcs.levelOne q) (κ.s_subset hq) v).1 :=
  coe_tangentFiberMap_apply _ _

/-- `B^m : bX^m → X^m`, sc-smooth. -/
abbrev bdryMapLift (m : ℕ) :
    ((bdry hX).lift m).P.IsScSmoothMap ((BundledMPolyfold.of PX).lift m).P
      ((bdry hX).liftMap (bdryMap hX) m) :=
  ((bdry hX).liftMap (bdryMap hX) m).isScSmoothMap

variable {k : ℕ}

open scoped Classical in
/-- **The restriction of `τ ∈ Ω^k(bX^m)` to the faces of `S`** (2021 p. 277, the integrand of
`∫_{∂S_{f+s}} τ`): on the face `{yᵢ = 0}` of the corner chart at `x`, at the point `q` with face
parameter `u` and on the face vectors `w`, the value `τ_b(β)` for a linear lift `(b, β)` of
`(ι^m q, Tι^m(κ.fiberMap (ιᵢ w)))` to `bX^m` (`linLiftForm`); `0` off the face domain. -/
def solFaceFormData (m : ℕ) (τ : (bdry hX).forms k m) : FaceFormData S n k := fun x i u =>
  if hu : u ∈ faceDomain (hcs.coords x).toQuadrantChart i then
    altCont (linLiftForm (bdryMapLift hX m) τ.1
      (solPt hcs m (facePoint (hcs.coords x).toQuadrantChart i u))
      (solVec hcs m (hcs.coords x) ((hcs.coords x).facePoint_mem_s hu) ∘ₗ
        (faceEmbedding i).toLinearMap))
  else 0

theorem solFaceFormData_apply_of_mem (m : ℕ) (τ : (bdry hX).forms k m) (x : S) (i : Fin (n + 1))
    {u : EuclideanSpace ℝ (Fin n)} (hu : u ∈ faceDomain (hcs.coords x).toQuadrantChart i)
    (w : Fin k → EuclideanSpace ℝ (Fin n)) :
    solFaceFormData hcs hX m τ x i u w = linLiftForm (bdryMapLift hX m) τ.1
      (solPt hcs m (facePoint (hcs.coords x).toQuadrantChart i u))
      (solVec hcs m (hcs.coords x) ((hcs.coords x).facePoint_mem_s hu) ∘ₗ
        (faceEmbedding i).toLinearMap) w := by
  rw [solFaceFormData, dif_pos hu]; rfl

theorem solFaceFormData_apply_of_notMem (m : ℕ) (τ : (bdry hX).forms k m) (x : S)
    (i : Fin (n + 1)) {u : EuclideanSpace ℝ (Fin n)}
    (hu : u ∉ faceDomain (hcs.coords x).toQuadrantChart i) :
    solFaceFormData hcs hX m τ x i u = 0 := by
  rw [solFaceFormData, dif_neg hu]

theorem solFaceFormData_add (m : ℕ) (τ σ : (bdry hX).forms k m) :
    solFaceFormData hcs hX m (τ + σ) = solFaceFormData hcs hX m τ + solFaceFormData hcs hX m σ := by
  funext x i u
  by_cases hu : u ∈ faceDomain (hcs.coords x).toQuadrantChart i
  · ext w
    rw [Pi.add_apply, Pi.add_apply, Pi.add_apply, ContinuousAlternatingMap.add_apply,
      solFaceFormData_apply_of_mem _ _ _ _ _ _ hu, solFaceFormData_apply_of_mem _ _ _ _ _ _ hu,
      solFaceFormData_apply_of_mem _ _ _ _ _ _ hu]
    change linLiftForm _ (τ.1 + σ.1) _ _ w = _
    rw [linLiftForm_add]
    rfl
  · simp only [Pi.add_apply, solFaceFormData_apply_of_notMem _ _ _ _ _ _ hu, add_zero]

theorem solFaceFormData_smul (m : ℕ) (c : ℝ) (τ : (bdry hX).forms k m) :
    solFaceFormData hcs hX m (c • τ) = c • solFaceFormData hcs hX m τ := by
  funext x i u
  by_cases hu : u ∈ faceDomain (hcs.coords x).toQuadrantChart i
  · ext w
    rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
      solFaceFormData_apply_of_mem _ _ _ _ _ _ hu, solFaceFormData_apply_of_mem _ _ _ _ _ _ hu]
    change linLiftForm _ (c • τ.1) _ _ w = _
    rw [linLiftForm_smul]
    rfl
  · simp only [Pi.smul_apply, solFaceFormData_apply_of_notMem _ _ _ _ _ _ hu, smul_zero]

namespace FaceLiftData

variable {hcs hX} {x : S} {i : Fin (n + 1)} (D : FaceLiftData hcs hX x i)

/-- The charted-space structure of the piece `U` (its `cornerChartedSpace`). -/
instance : ChartedSpace (EuclideanQuadrant n) D.U := D.Q.cornerChartedSpace D.hcsQ

instance : IsManifold (𝓠 n) ∞ D.U := isManifold_of_eq D.hcsQ rfl

/-- **The linear lift at `u ∈ U`**: `b = g^m(u)` and `L = Tg^m ∘ κ_U.fiberMap`. -/
theorem isLinLift (m : ℕ) (u : D.U) :
    IsLinLift (bdryMapLift hX m) (solPt hcs m (D.e u))
      (solVec hcs m (hcs.coords x) (D.e_mem_s u) ∘ₗ (faceEmbedding i).toLinearMap)
      (liftLevelOneMap (alongLift D.hcsQ D.gMap m).isScSmoothMap (D.hcsQ.levelOne u))
      ((tangentFiberMap (alongLift D.hcsQ D.gMap m).isScSmoothMap (D.hcsQ.levelOne u) :
        _ →ₗ[ℝ] _) ∘ₗ D.κQ.fiberMap (x := D.hcsQ.levelOne u) (D.κQ.s_subset (mem_univ _)))
    where
  base := by
    change (bdry hX).liftMap (bdryMap hX) m (alongLift D.hcsQ D.gMap m u) =
      solIncl hcs m (D.e u)
    rw [liftMap_alongLift D.hcsQ D.gMap (bdryMap hX) m u, D.bdryMap_comp_gMap]
    exact alongLift_comp (A := BundledMPolyfold.of PX) D.hcsQ hcs (subInclScMap hY) D.eMap m u
  vec := fun w => by
    change tangentMap (bdryMapLift hX m) (tangentFiberMap (alongLift D.hcsQ D.gMap m).isScSmoothMap
      (D.hcsQ.levelOne u) (D.κQ.fiberMap (D.κQ.s_subset (mem_univ _)) w)).1 =
      (solVec hcs m (hcs.coords x) (D.e_mem_s u) (faceEmbedding i w)).1
    have hfun : ⇑((bdry hX).liftMap (bdryMap hX) m) ∘ ⇑(alongLift D.hcsQ D.gMap m) =
        ⇑(solIncl hcs m) ∘ D.e := by
      funext u
      rw [Function.comp_apply, liftMap_alongLift D.hcsQ D.gMap (bdryMap hX) m u,
        D.bdryMap_comp_gMap]
      exact alongLift_comp (A := BundledMPolyfold.of PX) D.hcsQ hcs (subInclScMap hY) D.eMap m u
    rw [coe_tangentFiberMap_apply, coe_solVec, ← Function.comp_apply
        (f := tangentMap (bdryMapLift hX m)),
      ← tangentMap_comp (bdryMapLift hX m) (alongLift D.hcsQ D.gMap m).isScSmoothMap,
      tangentMap_congr_fun ((bdryMapLift hX m).comp (alongLift D.hcsQ D.gMap m).isScSmoothMap)
        ((solIncl hcs m).isScSmoothMap.comp D.isScSmoothMap_e) hfun,
      tangentMap_comp (solIncl hcs m).isScSmoothMap D.isScSmoothMap_e, Function.comp_apply,
      D.tangentMap_e_fiberMap]

/-- Lifts exist at the face points over `N`. -/
theorem exists_isLinLift (m : ℕ) (u : D.U) :
    ∃ (b : ((bdry hX).lift m).P.Level 1)
      (L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ((bdry hX).lift m).P.tangentFiber b),
      IsLinLift (bdryMapLift hX m) (solPt hcs m (D.e u))
        (solVec hcs m (hcs.coords x) (D.e_mem_s u) ∘ₗ (faceEmbedding i).toLinearMap) b L :=
  ⟨_, _, D.isLinLift m u⟩

/-- **The key identity**: on `U`, the face form of `τ` is the pull-back `(g^m)^*τ` of `τ` along
`g : U → bX`, read in the standard chart of `U` (`formsAlong`). -/
theorem solFaceFormData_eq_chartForm (m : ℕ) {τ : (bdry hX).forms k m}
    (hτ : IsFaceCompatible hX m τ.1) {u : EuclideanSpace ℝ (Fin n)} (hu : u ∈ D.U) :
    solFaceFormData hcs hX m τ x i u =
      ManifoldForm.chartForm (𝓠 n) D.κQ.toQuadrantChart (formsAlong D.hcsQ D.gMap m τ) u := by
  ext w
  have hy : u ∈ (D.κQ.toQuadrantChart.extend (𝓠 n)).target := by
    rw [quadrantPieceCoords_extend_target]; exact hu
  rw [solFaceFormData_apply_of_mem _ _ _ _ _ _ (D.U_subset_faceDomain hu)]
  change linLiftForm (bdryMapLift hX m) τ.1 (solPt hcs m (D.e ⟨u, hu⟩))
    (solVec hcs m (hcs.coords x) (D.e_mem_s ⟨u, hu⟩) ∘ₗ (faceEmbedding i).toLinearMap) w = _
  rw [linLiftForm_eq hτ (D.isLinLift m ⟨u, hu⟩), formsAlong_apply,
    chartForm_cornerForm_fiberMap D.hcsQ rfl D.κQ _ hy w]
  have hsymm : (D.κQ.toQuadrantChart.extend (𝓠 n)).symm u = ⟨u, hu⟩ :=
    quadrantPieceCoords_extend_symm _ _ hu
  change formPullback _ τ.1 (D.hcsQ.levelOne ⟨u, hu⟩) (fun j => D.κQ.fiberMap _ (w j)) = _
  rw [formPullback_apply]
  refine altFamily_congr τ.1 (congrArg _ (congrArg D.hcsQ.levelOne hsymm.symm)) _ _ fun j => ?_
  beta_reduce
  rw [coe_tangentFiberMap_apply]
  exact (congrArg (tangentMap _)
    (D.κQ.coe_fiberMap_congr (congrArg D.hcsQ.levelOne hsymm.symm) _ _ (w j))).trans
    (coe_tangentFiberMap_apply _ _).symm

end FaceLiftData

/-! ### The face forms of `S`: smoothness, chart changes, corners, `d` -/

variable (hdeg : ∀ a : S, (subPolyfold hY).degIndex a = PX.degIndex a)
include hdeg

/-- Lifts exist at every face point (for a tame `X` with `d_S = d_X`). -/
theorem exists_isLinLift_facePoint (m : ℕ) (x : S) (i : Fin (n + 1))
    {u : EuclideanSpace ℝ (Fin n)} (hu : u ∈ faceDomain (hcs.coords x).toQuadrantChart i) :
    ∃ (b : ((bdry hX).lift m).P.Level 1)
      (L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ((bdry hX).lift m).P.tangentFiber b),
      IsLinLift (bdryMapLift hX m) (solPt hcs m (facePoint (hcs.coords x).toQuadrantChart i u))
        (solVec hcs m (hcs.coords x) ((hcs.coords x).facePoint_mem_s hu) ∘ₗ
          (faceEmbedding i).toLinearMap) b L := by
  obtain ⟨D, rfl⟩ := exists_faceLiftData hX hdeg x i hu
  exact D.exists_isLinLift m ⟨D.u₀, D.mem_U_iff.2 ⟨D.u₀_mem, D.facePoint_u₀_mem⟩⟩

/-- **The face forms are `C^∞`** (locally `(g^m)^*τ`, `contDiffOn_chartForm_cornerForm`). -/
theorem contDiffOn_solFaceFormData (m : ℕ) {τ : (bdry hX).forms k m}
    (hτ : IsFaceCompatible hX m τ.1) (x : S) (i : Fin (n + 1)) :
    ContDiffOn ℝ ∞ (solFaceFormData hcs hX m τ x i)
      (faceDomain (hcs.coords x).toQuadrantChart i) := by
  intro u hu
  obtain ⟨D, rfl⟩ := exists_faceLiftData hX hdeg x i hu
  have huU : D.u₀ ∈ D.U := D.mem_U_iff.2 ⟨D.u₀_mem, D.facePoint_u₀_mem⟩
  have h1 : ContDiffOn ℝ ∞ (ManifoldForm.chartForm (𝓠 n) D.κQ.toQuadrantChart
      (formsAlong D.hcsQ D.gMap m τ)) D.U := by
    have h := contDiffOn_chartForm_cornerForm rfl D.κQ
      (formPullback_mem_scForms (alongLift D.hcsQ D.gMap m).isScSmoothMap τ.2)
    rw [quadrantPieceCoords_extend_target] at h
    exact h
  refine ((h1.congr fun z hz => ?_) D.u₀ huU).mono_of_mem_nhdsWithin (D.U_mem_nhdsWithin huU)
  exact D.solFaceFormData_eq_chartForm m hτ hz

/-- The face forms are compatible with the steps `Ωᵏ(∂Xᵐ) → Ωᵏ(∂Xᵐ⁺¹)` of (4.4). -/
theorem solFaceFormData_formsStep (m : ℕ) {τ : (bdry hX).forms k m} (hτ : τ ∈ bForms hX k m) :
    solFaceFormData hcs hX (m + 1) ((bdry hX).formsStep k m τ) = solFaceFormData hcs hX m τ := by
  funext x i u
  by_cases hu : u ∈ faceDomain (hcs.coords x).toQuadrantChart i
  · obtain ⟨D, rfl⟩ := exists_faceLiftData hX hdeg x i hu
    have huU : D.u₀ ∈ D.U := D.mem_U_iff.2 ⟨D.u₀_mem, D.facePoint_u₀_mem⟩
    rw [D.solFaceFormData_eq_chartForm (m + 1) (formLower_mem_bForms hX k hτ).1 huU,
      D.solFaceFormData_eq_chartForm m hτ.1 huU, formsAlong_formsStep]
  · rw [solFaceFormData_apply_of_notMem _ _ _ _ _ _ hu,
      solFaceFormData_apply_of_notMem _ _ _ _ _ _ hu]

variable [inst : ChartedSpace (EuclideanQuadrant (n + 1)) S]
  (hch : inst = (subPolyfold hY).cornerChartedSpace hcs)
include hch

omit hdeg in
/-- The chart at `x` is the Mathlib chart of the chosen corner coordinates. -/
theorem chartAt_eq_coords (x : S) :
    chartAt (EuclideanQuadrant (n + 1)) x = (hcs.coords x).toQuadrantChart :=
  chartAt_eq_of_eq hcs hch x

/-- **`ω|_S` extends `(j^*ω)|_{∂S}`** (`j^* = B^*`): on the face vectors, both are `ω` at
`Tι^m(κ.fiberMap (ιᵢ w))`. -/
theorem isExtendedBy_solFaceFormData_formsPullback (m : ℕ)
    (η : (BundledMPolyfold.of PX).forms k m) :
    IsExtendedBy (solFaceFormData hcs hX m (formsPullback (bdryMap hX) k m η))
      (scFormRestrict k hcs m η) := by
  intro x i u hu
  rw [chartAt_eq_coords hcs hch] at hu
  obtain ⟨b, L, hl⟩ := exists_isLinLift_facePoint hcs hX hdeg m x i hu
  ext w
  rw [faceRestriction_apply, chartAt_eq_coords hcs hch,
    solFaceFormData_apply_of_mem _ _ _ _ _ _ hu, coe_formsPullback, linLiftForm_formPullback _ hl]
  exact (chartForm_cornerForm_fiberMap hcs hch (hcs.coords x) _ hu (faceEmbedding i ∘ w)).trans
    rfl

/-- **`(dτ)|_{∂S} = d(τ|_{∂S})`** (`extDeriv_formsAlong` on each piece `U`). -/
theorem solFaceFormData_formsD (m : ℕ) {τ : (bdry hX).forms k m} (hτ : τ ∈ bForms hX k m) :
    solFaceFormData hcs hX (m + 1) ((bdry hX).formsD k m τ) =
      FaceFormData.d (solFaceFormData hcs hX m τ) := by
  funext x i u
  by_cases hu : u ∈ faceDomain (hcs.coords x).toQuadrantChart i
  · have huc : u ∈ faceDomain (chartAt (EuclideanQuadrant (n + 1)) x) i := by
      rw [chartAt_eq_coords hcs hch]; exact hu
    obtain ⟨D, rfl⟩ := exists_faceLiftData hX hdeg x i hu
    have huU : D.u₀ ∈ D.U := D.mem_U_iff.2 ⟨D.u₀_mem, D.facePoint_u₀_mem⟩
    have hy : D.u₀ ∈ (D.κQ.toQuadrantChart.extend (𝓠 n)).target := by
      rw [quadrantPieceCoords_extend_target]; exact huU
    rw [FaceFormData.d_apply_of_mem _ huc, chartAt_eq_coords hcs hch,
      D.solFaceFormData_eq_chartForm (m + 1) (extD_mem_bForms hX k hτ).1 huU,
      ← extDeriv_formsAlong D.gMap rfl m τ,
      ManifoldForm.chartForm_extDeriv_of_mem_target (mem_maximalAtlas_of_eq D.hcsQ rfl D.κQ)
        ((contMDiffForm_formsAlong D.gMap rfl m τ).of_le (by exact_mod_cast le_top)) hy,
      quadrantPieceCoords_extend_target]
    have h1 : extDerivWithin (solFaceFormData hcs hX m τ x i)
        (faceDomain (hcs.coords x).toQuadrantChart i) D.u₀ =
        extDerivWithin (solFaceFormData hcs hX m τ x i) D.U D.u₀ := by
      unfold extDerivWithin
      rw [fderivWithin_congr_set (D.U_eventuallyEq_faceDomain huU)]
    rw [h1]
    exact Filter.EventuallyEq.extDerivWithin_eq_of_mem (eventually_nhdsWithin_of_forall
      fun z hz => (D.solFaceFormData_eq_chartForm m hτ.1 hz).symm) huU
  · have huc : u ∉ faceDomain (chartAt (EuclideanQuadrant (n + 1)) x) i := by
      rw [chartAt_eq_coords hcs hch]; exact hu
    rw [solFaceFormData_apply_of_notMem _ _ _ _ _ _ hu]
    exact (FaceFormData.d_apply_of_notMem _ huc).symm

/-- **`τ|_{∂S}` is a form on the faces of `S`** (`IsChartFaceForm`): smooth, compatible under
chart changes and agreeing at the corners (the last two from the agreement of `τ` over `B`). -/
theorem isChartFaceForm_solFaceFormData (m : ℕ) {τ : (bdry hX).forms k m}
    (hτ : τ ∈ bForms hX k m) : IsChartFaceForm (solFaceFormData hcs hX m τ) where
  smooth x i := by
    rw [chartAt_eq_coords hcs hch]
    exact contDiffOn_solFaceFormData hcs hX hdeg m hτ.1 x i
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
    rw [solFaceFormData_apply_of_mem _ _ _ _ _ _ hu', solFaceFormData_apply_of_mem _ _ _ _ _ _ hu]
    refine linLiftForm_apply_congr hτ.1 (congrArg (solPt hcs m) (hq'.trans hq.symm))
      (exists_isLinLift_facePoint hcs hX hdeg m x' j hu')
      (exists_isLinLift_facePoint hcs hX hdeg m x i hu) _ _ fun l => ?_
    change (solVec hcs m (hcs.coords x') ((hcs.coords x').facePoint_mem_s hu')
      (faceEmbedding j (faceRestrict (chartChangeDeriv (𝓠 (n + 1)) (hcs.coords x).toQuadrantChart
        (hcs.coords x').toQuadrantChart p) i j (w l)))).1 =
      (solVec hcs m (hcs.coords x) ((hcs.coords x).facePoint_mem_s hu) (faceEmbedding i (w l))).1
    rw [← apply_faceEmbedding_eq (fun y => hA _ (faceEmbedding_apply_self i y)) (w l), coe_solVec,
      coe_solVec]
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
    rw [faceLift_apply, faceLift_apply, solFaceFormData_apply_of_mem _ _ _ _ _ _ hui,
      solFaceFormData_apply_of_mem _ _ _ _ _ _ huj]
    refine linLiftForm_apply_congr hτ.1 (congrArg (solPt hcs m) (hqi.trans hqj.symm))
      (exists_isLinLift_facePoint hcs hX hdeg m x i hui)
      (exists_isLinLift_facePoint hcs hX hdeg m x j huj) _ _ fun l => ?_
    change (solVec hcs m (hcs.coords x) ((hcs.coords x).facePoint_mem_s hui)
        (faceEmbedding i (faceProjection i (v l)))).1 =
      (solVec hcs m (hcs.coords x) ((hcs.coords x).facePoint_mem_s huj)
        (faceEmbedding j (faceProjection j (v l)))).1
    rw [faceEmbedding_faceProjection (hvi l), faceEmbedding_faceProjection (hvj l), coe_solVec,
      coe_solVec]
    exact congrArg (tangentMap _)
      ((hcs.coords x).coe_fiberMap_congr (congrArg hcs.levelOne (hqi.trans hqj.symm)) _ _ _)

/-! ### The linear map `Ω^k_∞(∂X) → Ω^k(∂S)` -/

/-- `Ω^k(∂X^m) → Ω^k(∂S)`, `τ ↦ τ|_{∂S}`, linear. -/
def solFaceFormAt (m : ℕ) : bForms hX k m →ₗ[ℝ] ChartFaceForm S n k where
  toFun τ := ⟨solFaceFormData hcs hX m τ.1, isChartFaceForm_solFaceFormData hcs hX hdeg hch m τ.2⟩
  map_add' τ σ := Subtype.ext (solFaceFormData_add hcs hX m τ.1 σ.1)
  map_smul' c τ := Subtype.ext (solFaceFormData_smul hcs hX m c τ.1)

theorem coe_solFaceFormAt (m : ℕ) (τ : bForms hX k m) :
    (solFaceFormAt hcs hX hdeg hch m τ : FaceFormData S n k) = solFaceFormData hcs hX m τ.1 :=
  rfl

theorem solFaceFormAt_agreeDFormsMap {i j : ℕ} (h : i ≤ j) (τ : bForms hX k i) :
    solFaceFormAt hcs hX hdeg hch j (agreeDFormsMap (bdryMap hX) k i j h τ) =
      solFaceFormAt hcs hX hdeg hch i τ := by
  apply Subtype.ext
  change solFaceFormData hcs hX j ((bdry hX).formsMap k i j h τ.1) =
    solFaceFormData hcs hX i τ.1
  induction j, h using Nat.le_induction with
  | base => rw [(bdry hX).formsMap_self k i]; rfl
  | succ j hij ih =>
    rw [(bdry hX).formsMap_succ k hij, LinearMap.comp_apply,
      solFaceFormData_formsStep hcs hX hdeg j (formsMap_mem_agreeDForms _ k hij τ.2), ih]

/-- **2021 Theorem 6.7.1 (p. 277; preprint 6.43), the boundary integrand: `τ ↦ τ|_{∂S}`**,
`Ω^k_∞(∂X) →ₗ[ℝ] Ω^k(∂S)`, for a sub-M-polyfold `S` of a tame `X` with a corner structure of
dimension `n + 1` and `d_S = d_X` (the solution sets in general position). -/
def solFaceForm : bFormsInfty hX k →ₗ[ℝ] ChartFaceForm S n k :=
  Module.DirectLimit.lift ℝ ℕ (fun i => ↥(agreeDForms (bdryMap hX) k i))
    (agreeDFormsMap (bdryMap hX) k) (solFaceFormAt hcs hX hdeg hch)
    fun _ _ h τ => solFaceFormAt_agreeDFormsMap hcs hX hdeg hch h τ

theorem solFaceForm_of (m : ℕ) (τ : bForms hX k m) :
    solFaceForm hcs hX hdeg hch (agreeDFormsInftyOf (bdryMap hX) k m τ) =
      solFaceFormAt hcs hX hdeg hch m τ :=
  Module.DirectLimit.lift_of _ _ _

/-- **The corner condition** of `τ|_{∂S}`: on two faces `{xᵢ = 0}`, `{x_j = 0}` through a corner
of a chart of `S`, the face forms agree on the vectors tangent to both faces (from the agreement
of `τ` over `B`, 2021 p. 198). -/
theorem solFaceForm_corner (τ : bFormsInfty hX k) (x : S) (i j : Fin (n + 1))
    {y : EuclideanSpace ℝ (Fin (n + 1))}
    (hy : y ∈ ((chartAt (EuclideanQuadrant (n + 1)) x).extend (𝓠 (n + 1))).target)
    (hyi : y i = 0) (hyj : y j = 0) (v : Fin k → EuclideanSpace ℝ (Fin (n + 1)))
    (hvi : ∀ l, v l i = 0) (hvj : ∀ l, v l j = 0) :
    faceLift i ((solFaceForm hcs hX hdeg hch τ : FaceFormData S n k) x i) y v =
      faceLift j ((solFaceForm hcs hX hdeg hch τ : FaceFormData S n k) x j) y v :=
  (solFaceForm hcs hX hdeg hch τ).2.corner x i j y hy hyi hyj v hvi hvj

/-- **`ω|_S` extends `(j^*ω)|_{∂S}`** on `Ω^k_∞`: `j^* = B^*` (`jStar`) followed by the
restriction to the faces of `S` is the face restriction of `ω|_S` (`formsInftyRestrict`). -/
theorem solFaceForm_isExtendedBy_jStar (η : (BundledMPolyfold.of PX).formsInfty k) :
    IsExtendedBy (solFaceForm hcs hX hdeg hch (jStar hX k η)) (formsInftyRestrict k hcs η) := by
  obtain ⟨m, η, rfl⟩ := Module.DirectLimit.exists_of η
  rw [jStar_of, solFaceForm_of, formsInftyRestrict_of]
  exact isExtendedBy_solFaceFormData_formsPullback hcs hX hdeg hch m η

/-- **`(dτ)|_{∂S} = d(τ|_{∂S})`** on `Ω^k_∞(∂X)` (`bFormsInftyD`, `ChartFaceForm.d`). -/
theorem solFaceForm_d [SigmaCompactSpace S] (τ : bFormsInfty hX k) :
    haveI := isManifold_of_eq hcs hch
    solFaceForm hcs hX hdeg hch (bFormsInftyD hX k τ) = (solFaceForm hcs hX hdeg hch τ).d := by
  have := isManifold_of_eq hcs hch
  refine agreeDFormsInfty_induction_on (bdryMap hX) k (C := fun τ =>
    solFaceForm hcs hX hdeg hch (bFormsInftyD hX k τ) = (solFaceForm hcs hX hdeg hch τ).d) τ
    fun m τ => ?_
  rw [bFormsInftyD, agreeDFormsInftyD_of, solFaceForm_of, solFaceForm_of]
  apply Subtype.ext
  rw [ChartFaceForm.coe_d, coe_solFaceFormAt, coe_solFaceFormAt, coe_agreeDFormsD]
  exact solFaceFormData_formsD hcs hX hdeg hch m τ.2

/-- **`∫_{∂S} (j^*ω)|_{∂S} = ∫_{∂S} ω|_S`** for compact `S` of dimension `n + 1` and
`ω ∈ Ωⁿ_∞(X)` (2021 p. 278, the boundary term of `Ψ` on `[dα, j^*α]`): the integral of the face
form (`ChartFaceForm.integral`) is the boundary integral of the extension `ω|_S`
(`faceIntegral_eq`). -/
theorem solFaceForm_jStar_integral [CompactSpace S]
    {o : TangentOrientation (𝓠 (n + 1)) S (n + 1)} (ho : o.IsContinuous (𝓠 (n + 1)) ∞)
    (η : (BundledMPolyfold.of PX).formsInfty n) :
    haveI := isManifold_of_eq hcs hch
    (solFaceForm hcs hX hdeg hch (jStar hX n η)).integral o =
      ManifoldForm.boundaryIntegral o (formsInftyRestrict n hcs η) := by
  have := isManifold_of_eq hcs hch
  exact faceIntegral_eq ho ((contMDiffForm_formsInftyRestrict hch η).of_le
    (by exact_mod_cast le_top)) isClosed_closure.isCompact
    (solFaceForm_isExtendedBy_jStar hcs hX hdeg hch η)

end SolFace

/-! ### The hypotheses hold for solution sets in general position -/

section SolutionSet

universe u₁ v₁

variable {X : Type u₁} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v₁} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

/-- **`d_S = d_X` for a solution set in general position** (2021 Theorem 4.2.11, the last
conclusion of `SolutionSetInGeneralPosition`), for every sub-M-polyfold structure (a proof). -/
theorem _root_.Polyfold.StrongBundle.SolutionSetInGeneralPosition.degIndex_eq {h : X → Y}
    (hgp : B.SolutionSetInGeneralPosition h) [ParacompactSpace (solutionSet P h)]
    (hY : PX.IsSubMPolyfold (solutionSet P h)) (a : solutionSet P h) :
    (subPolyfold hY).degIndex a = PX.degIndex a := by
  obtain ⟨-, -, -, hS, -, hrest⟩ := hgp
  exact hrest.2.2 a

end SolutionSet


end MPolyfold

end Polyfold
