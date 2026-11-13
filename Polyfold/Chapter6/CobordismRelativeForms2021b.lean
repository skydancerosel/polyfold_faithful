import Polyfold.Chapter4.BoundaryFormsPullback2021
import Polyfold.Chapter6.CobordismRelativeForms2021
import Polyfold.Chapter6.Theorem671Assembly2021

/-!
# The relative form on the cobordism `S_F` (2021 Theorem 6.7.1, p. 278)

Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021): in the proof of
Theorem 6.7.1 (p. 277–279; preprint Theorem 6.43) the invariants of two admissible sections are
compared through the form `p₁^*ω − dβ` on the cobordism `S_F ⊆ ℝ¹ × X`, with `j^*β = p₁^*τ` on
`∂S_F`.  `InvariantCobordism2021` states the existence of this form as the hypothesis
`CobordismRelativeForms`.  This file builds the form and removes the hypothesis from
Theorem 6.7.1.

## What is proved

* `MPolyfold.pullOver`, `isEndPullback_pullOver`, `contMDiffForm_smulFun_pullOver`: the pull-back
  `p₁^*γ` of a form `γ` on the Mathlib manifold `A` to the part of `A' ⊆ ℝ¹ × X` over an open set
  `T` of times where `A'` is `T × A`.
* `MPolyfold.faceRestriction_pullOver`: if `γ` extends `−τ|_{∂A}`, the face restriction of
  `p₁^*γ` is `−(p₁^*τ)|_{∂A'}` (`faceAlongData` of `BoundaryFormsPullback2021`).
* `MPolyfold.exists_closed_form_of_ends`: the closed form `(p₁^*ω)|_{A'} + dγ` with vanishing face
  restriction, reading as `ω|_{A_i} + dγ_i` on the product ends where the cut-offs are `1`.
* `MPolyfold.exists_rep_of_mem_ker_relD_zero`, `exists_rep_of_mem_ker_relD_succ`: a closed
  relative form has representatives `ω_N`, `τ_N` with `j^*ω_N = dτ_N` at one level.
* `cobordismRelativeFormsInner`: the relative form on `S_F^{k+1}`, reading as the integrands
  `a₀`, `a₁` on the inner ends `(0, 1/16) × S₀` and `(15/16, 1) × S₁`.
* `psiAt_eq_of_cobordism_of_orientation`: the cobordism identity `Ψ_{s₀} = Ψ_{s₁}` from
  `CobordismOrientation` alone; `psiAt_eq_of_admissible_of_orientation` and
  `psiAt_eq_of_homotopy_of_orientation`: steps (A) and (B) from `CobordismOrientationHyp` alone.
* `theorem_6_7_1_of_orientation`, `theorem_6_7_1_noBoundary_of_orientation`: Theorem 6.7.1 and
  its case `∂X = ∅` (p. 279) with the single hypothesis `CobordismOrientationHyp`.

## The inner ends

`CobordismRelativeForms` asks the form to be a pull-back on all of `(0, 1/8) × S₀` and
`(7/8, 1) × S₁`.  The cobordism data (`IsCobordismData`) make `S_F` a product for `t ≤ 1/8` and
for `t ≥ 7/8` only, so such a form has to be continued smoothly across `t = 1/8` where no product
structure is given; this needs an extension theorem for smooth forms from a closed half
(Seeley, Whitney), which is not in the library.  The cobordism argument does not need it:
`integral_eq_of_cutCobordism` works for any two product ends, and on the inner ends
`(0, 1/16) × S₀`, `(15/16, 1) × S₁` the cut-offs in `t` have room (`ρ₀ = 1` for `t ≤ 1/12`,
`ρ₀ = 0` for `t ≥ 5/48`; `ρ₁ = 0` for `t ≤ 43/48`, `ρ₁ = 1` for `t ≥ 11/12`).  The product
orientation of `CobordismOrientation` passes to the inner ends
(`ProductEnd.IsEndProductOrientation.of_subEnd`).  So `CobordismRelativeFormsHyp` itself is not
proved here; it is no longer used by `theorem_6_7_1_of_orientation`.

## Hypotheses

None is added: everything is proved for the cobordism data of `InvariantCobordism2021`, a tame
`X` and `AdmitsBumpFunctions` (for `Ψ`), as in `theorem_6_7_1_hyp`.
-/

open Set Filter Topology Manifold Module

noncomputable section

namespace Polyfold

universe u v

local notation "𝓠" => modelWithCornersEuclideanQuadrant

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- An open set of reals contains an open interval around each of its points. -/
theorem exists_Ioo_subset_of_isOpen {T : Set ℝ} (hT : IsOpen T) {t : ℝ} (ht : t ∈ T) :
    ∃ a b : ℝ, a < b ∧ t ∈ Ioo a b ∧ Ioo a b ⊆ T := by
  obtain ⟨a, b, hab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 (hT.mem_nhds ht)
  exact ⟨a, b, hab.1.trans hab.2, hab, hsub⟩

namespace MPolyfold

/-! ### Forms pulled back along `p₁` on a part of `A' ⊆ ℝ¹ × X` which is a product -/

section EndPull

open ManifoldForm BundledMPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  [ParacompactSpace ((Fin 1 → ℝ) × X)] {A : Set X} [ParacompactSpace A]
  {hA : PX.IsSubMPolyfold A} {A' : Set ((Fin 1 → ℝ) × X)} [ParacompactSpace A']
  (hA' : ((rnPolyfold 1).prod PX).IsSubMPolyfold A') {T : Set ℝ} (hT : IsOpen T)
  (hend : ∀ z : (Fin 1 → ℝ) × X, z.1 0 ∈ T → (z ∈ A' ↔ z.2 ∈ A)) (x₀ : A) {k : ℕ}
  (hcs : (subPolyfold hA).HasCornerStructureOfDim k)
  (hcs' : (subPolyfold hA').HasCornerStructureOfDim (k + 1))
  [instA : ChartedSpace (EuclideanQuadrant k) A]
  (hchA : instA = (subPolyfold hA).cornerChartedSpace hcs)
  [instA' : ChartedSpace (EuclideanQuadrant (k + 1)) A']
  (hchA' : instA' = (subPolyfold hA').cornerChartedSpace hcs')

/-- **The product end over an interval `(a, b) ⊆ T`** of a part `A' ⊆ ℝ¹ × X` which is
`T × A` over the open set `T` of times (`productEndOfSub`). -/
abbrev endOver {a b : ℝ} (hab : a < b) (hsub : Ioo a b ⊆ T) : ProductEnd k A A' a b :=
  productEndOfSub hA' hab (fun z hz => hend z (hsub hz)) x₀ hcs hcs' hchA hchA'

open scoped Classical in
/-- **The pull-back `p₁^*γ` over `T`** (the form `p₁^*β` on the ends of `S_F`, 2021 p. 278) of a
form `γ` on the Mathlib manifold `A`, on the part of `A' ⊆ ℝ¹ × X` over the open set `T` of
times, where `A'` is `T × A`: at `p`, `ProductEnd.pullAt` for a product end over an interval
around `t(p)` in `T`; `0` at the points not over `T`. -/
def pullOver {m : ℕ} (γ : ManifoldForm (𝓠 k) A m) : ManifoldForm (𝓠 (k + 1)) A' m := fun p =>
  if h : p.1.1 0 ∈ T then
    (endOver hA' hend x₀ hcs hcs' hchA hchA'
      (exists_Ioo_subset_of_isOpen hT h).choose_spec.choose_spec.1
      (exists_Ioo_subset_of_isOpen hT h).choose_spec.choose_spec.2.2).pullAt γ p
  else 0

/-- **`pullOver` reads as the pull-back of `γ` on every product end over `T`**
(`ProductEnd.IsEndPullback`), for every base point `x₀'` of the end. -/
theorem isEndPullback_pullOver {m : ℕ} (γ : ManifoldForm (𝓠 k) A m) (x₀' : A) {a b : ℝ}
    (hab : a < b) (hsub : Ioo a b ⊆ T) :
    (endOver hA' hend x₀' hcs hcs' hchA hchA' hab hsub).IsEndPullback
      (pullOver hA' hT hend x₀ hcs hcs' hchA hchA' γ) γ := by
  have := isManifold_of_eq hcs hchA
  have := isManifold_of_eq hcs' hchA'
  refine ProductEnd.isEndPullback_of_pullAt _ fun p hp => ?_
  have hpT : p.1.1 0 ∈ T := hsub hp
  refine ⟨_, _, endOver hA' hend x₀ hcs hcs' hchA hchA'
    (exists_Ioo_subset_of_isOpen hT hpT).choose_spec.choose_spec.1
    (exists_Ioo_subset_of_isOpen hT hpT).choose_spec.choose_spec.2.2,
    (exists_Ioo_subset_of_isOpen hT hpT).choose_spec.choose_spec.2.1, fun p' hp' => ?_, ?_⟩
  · exact Subtype.ext ((endProj_val_of_mem (fun z hz => hend z (hsub hz)) x₀ hp'.1).trans
      (endProj_val_of_mem (fun z hz => hend z (hsub hz)) x₀' hp'.1).symm)
  · rw [pullOver, dif_pos hpT]

/-- **A cut-off of `pullOver` is `C^∞`**: for a `C^∞` form `γ` on `A` and a smooth function `f`
on `A'` with support over `T`, `f · p₁^*γ` is a `C^∞` form on `A'`. -/
theorem contMDiffForm_smulFun_pullOver {m : ℕ} {γ : ManifoldForm (𝓠 k) A m}
    (hγ : ContMDiffForm (𝓠 k) ∞ γ) {f : A' → ℝ} (hf : ContMDiff (𝓠 (k + 1)) 𝓘(ℝ) ∞ f)
    (hsupp : ∀ p ∈ _root_.tsupport f, p.1.1 0 ∈ T) :
    ContMDiffForm (𝓠 (k + 1)) ∞
      (smulFun f (pullOver hA' hT hend x₀ hcs hcs' hchA hchA' γ)) := by
  have := isManifold_of_eq hcs hchA
  have := isManifold_of_eq hcs' hchA'
  refine ProductEnd.contMDiffForm_smulFun_of_isEndPullback hγ hf fun p hp => ?_
  obtain ⟨a, b, hab, ht, hsub⟩ := exists_Ioo_subset_of_isOpen hT (hsupp p hp)
  exact ⟨a, b, endOver hA' hend x₀ hcs hcs' hchA hchA' hab hsub, ht,
    isEndPullback_pullOver hA' hT hend x₀ hcs hcs' hchA hchA' γ x₀ hab hsub⟩

end EndPull

/-! ### The face restriction of `p₁^*γ` -/

section EndFace

open ManifoldForm BundledMPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  [ParacompactSpace ((Fin 1 → ℝ) × X)] {A : Set X} [ParacompactSpace A]
  {hA : PX.IsSubMPolyfold A} {A' : Set ((Fin 1 → ℝ) × X)} [ParacompactSpace A']
  (hA' : ((rnPolyfold 1).prod PX).IsSubMPolyfold A') {T : Set ℝ} (hT : IsOpen T)
  (hend : ∀ z : (Fin 1 → ℝ) × X, z.1 0 ∈ T → (z ∈ A' ↔ z.2 ∈ A)) (x₀ : A) {n : ℕ}
  (hcs : (subPolyfold hA).HasCornerStructureOfDim (n + 1))
  (hcs' : (subPolyfold hA').HasCornerStructureOfDim (n + 1 + 1))
  [instA : ChartedSpace (EuclideanQuadrant (n + 1)) A]
  (hchA : instA = (subPolyfold hA).cornerChartedSpace hcs)
  [instA' : ChartedSpace (EuclideanQuadrant (n + 1 + 1)) A']
  (hchA' : instA' = (subPolyfold hA').cornerChartedSpace hcs')
  (hX : PX.IsTame)

/-- The projection `p₁ : A' → X`, `(t, x) ↦ x`, of a sub-M-polyfold `A' ⊆ ℝ¹ × X`, as an
`ScMap`. -/
abbrev sndIncl : ScMap (subPolyfold hA') (BundledMPolyfold.of PX).P :=
  (prXScMap PX).comp (subInclScMap hA')

include hX in
/-- `d_{A'} = d_X ∘ p₁` when `d_{A'} = d_{ℝ¹ × X}` (`d_{ℝ¹ × X}(t, x) = d_X(x)`,
`isTame_prod`). -/
theorem degIndex_sndIncl
    (hdeg' : ∀ a : A', (subPolyfold hA').degIndex a = ((rnPolyfold 1).prod PX).degIndex a)
    (a : A') : (subPolyfold hA').degIndex a = PX.degIndex (sndIncl hA' a) := by
  rw [hdeg', (isTame_prod (rnPolyfold 1) PX rnPolyfold_isTame hX).2 a.1.1 a.1.2, degIndex_rn,
    zero_add]
  rfl

/-- **The face restriction of `p₁^*γ`** (the step "`j^*β = p₁^*τ` on the ends" of 2021 p. 278):
if `γ` on `A` extends `−τ|_{∂A}`, then over `T` the face restriction of `p₁^*γ` on `A'` is
`−(p₁^*τ)|_{∂A'}` (`faceAlongData` along `p₁`), at the face points on no other face.  Proof: in
the product chart of the chart of `A` at the projection, the face is `(a, b)` times a face of
`A`, and the face vectors are mapped by `Tp₁` to face vectors of `A`
(`tangentMap_prodRn_fiberMap`). -/
theorem faceRestriction_pullOver
    (hdeg : ∀ a : A, (subPolyfold hA).degIndex a = PX.degIndex a)
    (hdeg' : ∀ a : A', (subPolyfold hA').degIndex a = ((rnPolyfold 1).prod PX).degIndex a)
    {d M : ℕ} {τ : (bdry hX).forms d M} (hτ : IsFaceCompatible hX M τ.1)
    {γ : ManifoldForm (𝓠 (n + 1)) A d}
    (hext : IsExtendedBy ((-1 : ℝ) • faceAlongData hcs (subInclScMap hA) hX M τ) γ)
    (x : A') (i : Fin (n + 1 + 1)) {u : EuclideanSpace ℝ (Fin (n + 1))}
    (hu : u ∈ openFaceDomain (chartAt (EuclideanQuadrant (n + 1 + 1)) x) i)
    (hpT : (facePoint (chartAt (EuclideanQuadrant (n + 1 + 1)) x) i u).1.1 0 ∈ T) :
    faceRestriction (pullOver hA' hT hend x₀ hcs hcs' hchA hchA' γ) x i u =
      ((-1 : ℝ) • faceAlongData hcs' (sndIncl hA') hX M τ) x i u := by
  have := isManifold_of_eq hcs hchA
  have := isManifold_of_eq hcs' hchA'
  have hX' : ((rnPolyfold 1).prod PX).IsTame := prod_rn_isTame hX
  have hcx := chartAt_eq_coords hcs' hchA' x
  rw [hcx] at hu hpT
  set κ'' := hcs'.coords x with hκ''
  set e := κ''.toQuadrantChart with he_def
  have hud : u ∈ faceDomain e i := openFaceDomain_subset _ _ hu
  set p := facePoint e i u with hp_def
  have hp : p ∈ e.source := facePoint_mem_source hud
  have hep : e.extend (𝓠 (n + 1 + 1)) p = faceEmbedding i u := extend_facePoint hud
  have hi : ∀ l, e.extend (𝓠 (n + 1 + 1)) p l = 0 ↔ l = i := fun l => by
    rw [hep]; exact faceEmbedding_eq_zero_iff hu l
  obtain ⟨a, b, hab, ht, hsub⟩ := exists_Ioo_subset_of_isOpen hT hpT
  have hend' : ∀ z : (Fin 1 → ℝ) × X, z.1 0 ∈ Ioo a b → (z ∈ A' ↔ z.2 ∈ A) :=
    fun z hz => hend z (hsub hz)
  set q₀ := endProj A x₀ p with hq₀_def
  set κ := hcs.coords q₀ with hκ
  set κ' := κ.prodRn hA' hab hend' x₀ with hκ'
  set e' := κ'.toQuadrantChart with he'_def
  have hq₀ : q₀ ∈ κ.s := hcs.mem_coords q₀
  have hp' : p ∈ e'.source := (CornerCoords.mem_prodRn_s hA' hab hend' x₀ κ).2 ⟨ht, hq₀⟩
  have he := mem_maximalAtlas_of_eq hcs' hchA' κ''
  have he' := mem_maximalAtlas_of_eq hcs' hchA' κ'
  obtain ⟨j', hj', hAj, -⟩ := exists_face_chartChange he he' hp hp' hi
  have hcoord : ∀ l, e'.extend (𝓠 (n + 1 + 1)) p l =
      (Fin.cons (p.1.1 0 - a) (κ.coord q₀) : Fin (n + 1 + 1) → ℝ) l := fun l => by
    rw [he'_def, κ'.extend_eq_toLp_coord hp', CornerCoords.prodRn_coord]
  obtain ⟨j, rfl⟩ : ∃ j : Fin (n + 1), j' = j.succ := by
    rcases Fin.eq_zero_or_eq_succ j' with rfl | h
    · have h0 := (hj' 0).2 rfl
      rw [hcoord, Fin.cons_zero] at h0
      linarith [ht.1]
    · exact h
  have hc₀ : chartAt (EuclideanQuadrant (n + 1)) q₀ = κ.toQuadrantChart :=
    chartAt_eq_coords hcs hchA q₀
  set z₀ := κ.toQuadrantChart.extend (𝓠 (n + 1)) q₀ with hz₀_def
  have hz₀ : z₀ = WithLp.toLp 2 (κ.coord q₀) := κ.extend_eq_toLp_coord hq₀
  have hz₀j : z₀ j = 0 := by
    have := (hj' j.succ).2 rfl
    rw [hcoord, Fin.cons_succ] at this
    rw [hz₀]; exact this
  set u₀ := faceProjection j z₀ with hu₀_def
  have hu₀ : u₀ ∈ faceDomain κ.toQuadrantChart j :=
    faceProjection_extend_mem_faceDomain hq₀ hz₀j
  have hfp₀ : facePoint κ.toQuadrantChart j u₀ = q₀ := facePoint_faceProjection_extend hq₀ hz₀j
  set E := endOver hA' hend x₀ hcs hcs' hchA hchA' hab hsub with hE
  have heqv : E.chart κ.toQuadrantChart ≈ e' := endChart_eqOnSource hA' hab hend' x₀ κ
  set y' := e'.extend (𝓠 (n + 1 + 1)) p with hy'_def
  have hy'e : y' ∈ (e'.extend (𝓠 (n + 1 + 1))).target :=
    (e'.extend _).map_source (by rwa [e'.extend_source])
  have hy' : y' ∈ ((E.chart κ.toQuadrantChart).extend (𝓠 (n + 1 + 1))).target := by
    rw [OpenPartialHomeomorph.extend_target] at hy'e ⊢
    rwa [heqv.target_eq]
  have hpull := isEndPullback_pullOver hA' hT hend x₀ hcs hcs' hchA hchA' γ x₀ hab hsub q₀ y'
    (by rw [hc₀]; exact hy')
  rw [hc₀, chartForm_eq_of_eqOnSource heqv _ hy'] at hpull
  have hty' : tailE y' = z₀ := by
    ext l
    rw [tailE_apply, hy'_def, hcoord, Fin.cons_succ, hz₀]
  have hGG : ∀ r : A', r.1.1 0 ∈ Ioo a b →
      alongLift hcs' (A := BundledMPolyfold.of PX) (sndIncl hA') M r =
        alongLift hcs (A := BundledMPolyfold.of PX) (subInclScMap hA) M (endProj A x₀ r) :=
    fun r hr => (BundledMPolyfold.of PX).incl_injective M
      ((incl_alongLift hcs' (A := BundledMPolyfold.of PX) (sndIncl hA') M r).trans
        (((endProj_val_of_mem hend' x₀ hr).symm : r.1.2 = (endProj A x₀ r).1).trans
          (incl_alongLift hcs (A := BundledMPolyfold.of PX) (subInclScMap hA) M _).symm))
  ext w
  have hL : faceRestriction (pullOver hA' hT hend x₀ hcs hcs' hchA hchA' γ) x i u w =
      ManifoldForm.chartForm (𝓠 (n + 1 + 1)) e' (pullOver hA' hT hend x₀ hcs hcs' hchA hchA' γ) y'
        (chartChangeDeriv (𝓠 (n + 1 + 1)) e e' p ∘ faceEmbedding i ∘ w) := by
    rw [faceRestriction_apply, hcx, ← hep]
    exact (chartForm_chartChangeDeriv_apply he he' _ hp hp' _).symm
  set v : Fin d → EuclideanSpace ℝ (Fin (n + 1)) := fun l =>
    tailE (chartChangeDeriv (𝓠 (n + 1 + 1)) e e' p (faceEmbedding i (w l))) with hv_def
  have hvj : ∀ l, v l j = 0 := fun l => hAj _ (faceEmbedding_apply_self i (w l))
  have hv : ∀ l, faceEmbedding j (faceProjection j (v l)) = v l := fun l =>
    faceEmbedding_faceProjection (hvj l)
  have hR := hext q₀ j (by rw [hc₀]; exact hu₀)
  have h1 : ManifoldForm.chartForm (𝓠 (n + 1)) κ.toQuadrantChart γ (tailE y') v =
      faceRestriction γ q₀ j u₀ (faceProjection j ∘ v) := by
    rw [faceRestriction_apply, hc₀, hty',
      show faceEmbedding j u₀ = z₀ from faceEmbedding_faceProjection hz₀j,
      show (faceEmbedding j ∘ (faceProjection j ∘ v)) = v from funext hv]
  rw [hL, hpull, tailPull_apply]
  change ManifoldForm.chartForm (𝓠 (n + 1)) κ.toQuadrantChart γ (tailE y') v = _
  rw [h1, hR]
  simp only [Pi.smul_apply, ContinuousAlternatingMap.smul_apply]
  congr 1
  refine (faceAlongData_apply_of_mem hcs (subInclScMap hA) hX M τ q₀ j hu₀ _).trans
    (Eq.trans ?_ (faceAlongData_apply_of_mem hcs' (sndIncl hA') hX M τ x i hud w).symm)
  refine linLiftForm_apply_congr hτ ?_
    (exists_isLinLift_facePoint_along hcs (subInclScMap hA) hX hX hdeg hdeg M q₀ j hu₀)
    (exists_isLinLift_facePoint_along hcs' (sndIncl hA') hX hX' hdeg'
      (degIndex_sndIncl hA' hX hdeg') M x i hud) _ _ fun l => ?_
  · apply level_ext
    rw [levelVal_liftLevelOneMap, levelVal_liftLevelOneMap]
    exact (congrArg (alongLift hcs (A := BundledMPolyfold.of PX) (subInclScMap hA) M) hfp₀).trans
      (hGG p ht).symm
  · have e1 := coe_alongVec hcs (subInclScMap hA) M κ (κ.facePoint_mem_s hu₀)
      (faceEmbedding j (faceProjection j (v l)))
    have e2 := coe_alongVec hcs' (sndIncl hA') M κ'' (κ''.facePoint_mem_s hud)
      (faceEmbedding i (w l))
    refine e1.trans (Eq.trans ?_ e2.symm)
    have h3 : (κ.fiberMap (x := hcs.levelOne (facePoint κ.toQuadrantChart j u₀))
        (κ.s_subset (κ.facePoint_mem_s hu₀)) (faceEmbedding j (faceProjection j (v l)))).1 =
        (κ.fiberMap (x := hcs.levelOne q₀) (κ.s_subset hq₀) (v l)).1 := by
      rw [hv l]
      exact κ.coe_fiberMap_congr (congrArg hcs.levelOne hfp₀) _ _ (v l)
    have h2 := tangentMap_prodRn_fiberMap hA' hab hend' x₀
      (alongIncl hcs (subInclScMap hA) M).isScSmoothMap
      (alongIncl hcs' (sndIncl hA') M).isScSmoothMap hGG κ (p := hcs'.levelOne p)
      (κ'.s_subset hp') (x := hcs.levelOne q₀) (κ.s_subset hq₀) rfl
      (chartChangeDeriv (𝓠 (n + 1 + 1)) e e' p (faceEmbedding i (w l)))
    exact ((congrArg (tangentMap _) h3).trans h2.symm).trans
      (congrArg (tangentMap _) (congrArg Subtype.val
        (fiberMap_chartChange hchA' κ'' κ' hp hp' (faceEmbedding i (w l)))))

include hT in
/-- **The pull-back `p₁^*γ` over `T`, with its properties** (also for `A = ∅`, where it is
`0`): a form `P` on `A'` such that every cut-off of `P` supported over `T` is `C^∞`, the face
restriction of `P` over `T` is `−(p₁^*τ)|_{∂A'}`, and `P` reads as the pull-back of `γ` on every
product end over `T`. -/
theorem exists_end_form
    (hdeg : ∀ a : A, (subPolyfold hA).degIndex a = PX.degIndex a)
    (hdeg' : ∀ a : A', (subPolyfold hA').degIndex a = ((rnPolyfold 1).prod PX).degIndex a)
    {d M : ℕ} {τ : (bdry hX).forms d M} (hτ : IsFaceCompatible hX M τ.1)
    {γ : ManifoldForm (𝓠 (n + 1)) A d} (hγ : ContMDiffForm (𝓠 (n + 1)) ∞ γ)
    (hext : IsExtendedBy ((-1 : ℝ) • faceAlongData hcs (subInclScMap hA) hX M τ) γ) :
    ∃ P : ManifoldForm (𝓠 (n + 1 + 1)) A' d,
      (∀ f : A' → ℝ, ContMDiff (𝓠 (n + 1 + 1)) 𝓘(ℝ) ∞ f →
        (∀ p ∈ _root_.tsupport f, p.1.1 0 ∈ T) →
          ContMDiffForm (𝓠 (n + 1 + 1)) ∞ (smulFun f P)) ∧
      (∀ (x : A') (i : Fin (n + 1 + 1)),
        ∀ u ∈ openFaceDomain (chartAt (EuclideanQuadrant (n + 1 + 1)) x) i,
          (facePoint (chartAt (EuclideanQuadrant (n + 1 + 1)) x) i u).1.1 0 ∈ T →
            faceRestriction P x i u =
              ((-1 : ℝ) • faceAlongData hcs' (sndIncl hA') hX M τ) x i u) ∧
      ∀ (x₀ : A) {a b : ℝ} (hab : a < b) (hsub : Ioo a b ⊆ T),
        (endOver hA' hend x₀ hcs hcs' hchA hchA' hab hsub).IsEndPullback P γ := by
  rcases isEmpty_or_nonempty A with hE | ⟨⟨x₀⟩⟩
  · refine ⟨0, fun f _ _ => ?_, fun x i u _ hpT => ?_, fun x₀ => (hE.false x₀).elim⟩
    · have h0 : smulFun f (0 : ManifoldForm (𝓠 (n + 1 + 1)) A' d) = 0 := by
        funext p; rw [smulFun_apply, Pi.zero_apply, smul_zero]
      rw [h0]; exact contMDiffForm_zero_form _
    · exact (hE.false ⟨_, (hend _ hpT).1
        (facePoint (chartAt (EuclideanQuadrant (n + 1 + 1)) x) i u).2⟩).elim
  · exact ⟨pullOver hA' hT hend x₀ hcs hcs' hchA hchA' γ,
      fun f hf hsupp => contMDiffForm_smulFun_pullOver hA' hT hend x₀ hcs hcs' hchA hchA' hγ hf
        hsupp,
      fun x i u hu hpT => faceRestriction_pullOver hA' hT hend x₀ hcs hcs' hchA hchA' hX hdeg
        hdeg' hτ hext x i hu hpT,
      fun x₀' _ _ hab hsub =>
        isEndPullback_pullOver hA' hT hend x₀ hcs hcs' hchA hchA' γ x₀' hab hsub⟩

end EndFace

/-! ### The closed form `p₁^*ω + dγ` on a part of `ℝ¹ × X` with two product ends -/

section TwoEnds

open ManifoldForm BundledMPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  [ParacompactSpace ((Fin 1 → ℝ) × X)] {A' : Set ((Fin 1 → ℝ) × X)} [ParacompactSpace A']
  (hA' : ((rnPolyfold 1).prod PX).IsSubMPolyfold A') {n : ℕ}
  (hcs' : (subPolyfold hA').HasCornerStructureOfDim (n + 1))
  [instA' : ChartedSpace (EuclideanQuadrant (n + 1)) A']
  (hchA' : instA' = (subPolyfold hA').cornerChartedSpace hcs') (hX : PX.IsTame)
  (hdeg' : ∀ a : A', (subPolyfold hA').degIndex a = ((rnPolyfold 1).prod PX).degIndex a)

include hchA' in
/-- `(p₁^*ω)|_{A'}` is closed when `ω` is. -/
theorem extDeriv_formsInftyAlong_sndIncl_eq_zero {d : ℕ}
    (ω : (BundledMPolyfold.of PX).formsInfty d)
    (hd : (BundledMPolyfold.of PX).formsInftyD d ω = 0) :
    ManifoldForm.extDeriv (formsInftyAlong d hcs' (sndIncl hA') ω) = 0 := by
  rw [extDeriv_formsInftyAlong (sndIncl hA') hchA' ω, hd, map_zero]

include hchA' hdeg' in
/-- **`(p₁^*ω)|_{A'}` extends `(p₁^* j^*ω)|_{∂A'}`** (`isExtendedBy_faceAlongData_formsPullback`
on representatives). -/
theorem isExtendedBy_formsInftyAlong_sndIncl {d N : ℕ} (ωN : (BundledMPolyfold.of PX).forms d N) :
    IsExtendedBy (faceAlongData hcs' (sndIncl hA') hX N (formsPullback (bdryMap hX) d N ωN))
      (formsInftyAlong d hcs' (sndIncl hA') ((BundledMPolyfold.of PX).formsInftyOf d N ωN)) := by
  rw [formsInftyAlong_of]
  exact isExtendedBy_faceAlongData_formsPullback hcs' (sndIncl hA') hX (prod_rn_isTame hX) hdeg'
    (degIndex_sndIncl hA' hX hdeg') hchA' N ωN

end TwoEnds

section TwoEndsSucc

open ManifoldForm BundledMPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  [ParacompactSpace ((Fin 1 → ℝ) × X)] {A' : Set ((Fin 1 → ℝ) × X)} [ParacompactSpace A']
  (hA' : ((rnPolyfold 1).prod PX).IsSubMPolyfold A') {n : ℕ}
  (hcs' : (subPolyfold hA').HasCornerStructureOfDim (n + 1 + 1))
  [instA' : ChartedSpace (EuclideanQuadrant (n + 1 + 1)) A']
  (hchA' : instA' = (subPolyfold hA').cornerChartedSpace hcs') (hX : PX.IsTame)
  (hdeg' : ∀ a : A', (subPolyfold hA').degIndex a = ((rnPolyfold 1).prod PX).degIndex a)

include hdeg' in
/-- **The relative form on a part `A'` of `ℝ¹ × X` with two product ends** (the form
`p₁^*ω − dβ` on `S_F`, proof of 2021 Theorem 6.7.1, p. 278; preprint Theorem 6.43): let `A'` be
`T₀ × A₀` over the open set `T₀` of times and `T₁ × A₁` over `T₁`, with compact slabs; let
`(ω, τ)` be represented by `ω_N`, `τ_N` with `dω = 0` and `j^*ω_N = dτ_N`; let `γ_i` be `C^∞`
forms on `A_i` extending `−τ|_{∂A_i}`, and `ρ₀`, `ρ₁` cut-offs in the time supported over `T₀`,
`T₁` with `ρ₀ + ρ₁ = 1` outside `[l, u]`.  Then there is a closed `C^∞` form
`A = (p₁^*ω)|_{A'} + dγ` on `A'` with vanishing face restriction, which on the product ends where
`ρ_i = 1` reads as the pull-back of `ω|_{A_i} + dγ_i`.  Here `γ` extends
`−(p₁^*τ)|_{∂A'}` and is `p₁^*γ_i` where `ρ_i = 1` (`exists_glued_extension`,
`exists_end_form`). -/
theorem exists_closed_form_of_ends [SigmaCompactSpace A']
    (hslab : ∀ c c' : ℝ, IsCompact {p : A' | p.1.1 0 ∈ Icc c c'})
    {A₀ : Set X} [ParacompactSpace A₀] {hA₀ : PX.IsSubMPolyfold A₀}
    (hcs₀ : (subPolyfold hA₀).HasCornerStructureOfDim (n + 1))
    [inst₀ : ChartedSpace (EuclideanQuadrant (n + 1)) A₀]
    (hch₀ : inst₀ = (subPolyfold hA₀).cornerChartedSpace hcs₀)
    (hdeg₀ : ∀ a : A₀, (subPolyfold hA₀).degIndex a = PX.degIndex a)
    {T₀ : Set ℝ} (hT₀ : IsOpen T₀)
    (hend₀ : ∀ z : (Fin 1 → ℝ) × X, z.1 0 ∈ T₀ → (z ∈ A' ↔ z.2 ∈ A₀))
    {A₁ : Set X} [ParacompactSpace A₁] {hA₁ : PX.IsSubMPolyfold A₁}
    (hcs₁ : (subPolyfold hA₁).HasCornerStructureOfDim (n + 1))
    [inst₁ : ChartedSpace (EuclideanQuadrant (n + 1)) A₁]
    (hch₁ : inst₁ = (subPolyfold hA₁).cornerChartedSpace hcs₁)
    (hdeg₁ : ∀ a : A₁, (subPolyfold hA₁).degIndex a = PX.degIndex a)
    {T₁ : Set ℝ} (hT₁ : IsOpen T₁)
    (hend₁ : ∀ z : (Fin 1 → ℝ) × X, z.1 0 ∈ T₁ → (z ∈ A' ↔ z.2 ∈ A₁))
    {N : ℕ} (ω : (BundledMPolyfold.of PX).formsInfty (n + 1))
    (ωN : (BundledMPolyfold.of PX).forms (n + 1) (N + 1)) (τN : bForms hX n N)
    (hω : ω = (BundledMPolyfold.of PX).formsInftyOf (n + 1) (N + 1) ωN)
    (hB : formsPullback (bdryMap hX) (n + 1) (N + 1) ωN = (bdry hX).formsD n N τN.1)
    (hd : (BundledMPolyfold.of PX).formsInftyD (n + 1) ω = 0)
    {γ₀ : ManifoldForm (𝓠 (n + 1)) A₀ n} (hγ₀ : ContMDiffForm (𝓠 (n + 1)) ∞ γ₀)
    (hext₀ : IsExtendedBy ((-1 : ℝ) • faceAlongData hcs₀ (subInclScMap hA₀) hX N τN.1) γ₀)
    {γ₁ : ManifoldForm (𝓠 (n + 1)) A₁ n} (hγ₁ : ContMDiffForm (𝓠 (n + 1)) ∞ γ₁)
    (hext₁ : IsExtendedBy ((-1 : ℝ) • faceAlongData hcs₁ (subInclScMap hA₁) hX N τN.1) γ₁)
    {ρ₀ ρ₁ : ℝ → ℝ} (hρ₀ : ContDiff ℝ ∞ ρ₀) (hρ₁ : ContDiff ℝ ∞ ρ₁) {C₀ C₁ : Set ℝ}
    (hC₀ : IsClosed C₀) (hC₀T : C₀ ⊆ T₀) (hρ₀C : ∀ s, s ∉ C₀ → ρ₀ s = 0)
    (hC₁ : IsClosed C₁) (hC₁T : C₁ ⊆ T₁) (hρ₁C : ∀ s, s ∉ C₁ → ρ₁ s = 0) {l u : ℝ}
    (hmid : ∀ s, s ∉ Icc l u → ρ₀ s + ρ₁ s = 1) :
    ∃ F : ManifoldForm (𝓠 (n + 1 + 1)) A' (n + 1),
      ContMDiffForm (𝓠 (n + 1 + 1)) ∞ F ∧ ManifoldForm.extDeriv F = 0 ∧
      (∀ x i, EqOn (faceRestriction F x i) 0
        (openFaceDomain (chartAt (EuclideanQuadrant (n + 1 + 1)) x) i)) ∧
      (∀ (x₀ : A₀) {a b : ℝ} (hab : a < b) (hsub : Ioo a b ⊆ T₀),
        (∀ s ∈ Ioo a b, ρ₀ s = 1 ∧ ρ₁ s = 0) →
          (endOver hA' hend₀ x₀ hcs₀ hcs' hch₀ hchA' hab hsub).IsEndPullback F
            (formsInftyRestrict (n + 1) hcs₀ ω + ManifoldForm.extDeriv γ₀)) ∧
      ∀ (x₁ : A₁) {a b : ℝ} (hab : a < b) (hsub : Ioo a b ⊆ T₁),
        (∀ s ∈ Ioo a b, ρ₁ s = 1 ∧ ρ₀ s = 0) →
          (endOver hA' hend₁ x₁ hcs₁ hcs' hch₁ hchA' hab hsub).IsEndPullback F
            (formsInftyRestrict (n + 1) hcs₁ ω + ManifoldForm.extDeriv γ₁) := by
  have := isManifold_of_eq hcs' hchA'
  have := isManifold_of_eq hcs₀ hch₀
  have := isManifold_of_eq hcs₁ hch₁
  have hX' : ((rnPolyfold 1).prod PX).IsTame := prod_rn_isTame hX
  have hdegG := degIndex_sndIncl hA' hX hdeg'
  set σ : FaceFormData A' (n + 1) n := faceAlongData hcs' (sndIncl hA') hX N τN.1 with hσ_def
  have hσ : IsChartFaceForm σ :=
    isChartFaceForm_faceAlongData hcs' (sndIncl hA') hX hX' hdeg' hdegG hchA' N τN.2
  have hτ : IsFaceCompatible hX N τN.1.1 := ((mem_bForms hX n).1 τN.2).1
  obtain ⟨P₀, hP₀s, hP₀f, hP₀e⟩ := exists_end_form hA' hT₀ hend₀ hcs₀ hcs' hch₀ hchA' hX hdeg₀
    hdeg' hτ hγ₀ hext₀
  obtain ⟨P₁, hP₁s, hP₁f, hP₁e⟩ := exists_end_form hA' hT₁ hend₁ hcs₁ hcs' hch₁ hchA' hX hdeg₁
    hdeg' hτ hγ₁ hext₁
  have ht : ContMDiff (𝓠 (n + 1 + 1)) 𝓘(ℝ) ∞ (fun p : A' => p.1.1 0) :=
    contMDiff_comp_time hcs' hchA' contDiff_id
  have hsupp : ∀ {ρ : ℝ → ℝ} {C : Set ℝ}, IsClosed C → (∀ s, s ∉ C → ρ s = 0) →
      _root_.tsupport (fun p : A' => ρ (p.1.1 0)) ⊆ (fun p : A' => p.1.1 0) ⁻¹' C :=
    fun hC hρC => closure_minimal
      (fun q hq => by_contra fun h => Function.mem_support.1 hq (hρC _ h))
      (hC.preimage ht.continuous)
  obtain ⟨γ, hγ, hextγ, hγ0, hγ1⟩ := exists_glued_extension ht hslab hσ hρ₀ hρ₁
    (hP₀s _ (hρ₀.contMDiff.comp ht) fun p hp => hC₀T (hsupp hC₀ hρ₀C hp))
    (hP₁s _ (hρ₁.contMDiff.comp ht) fun p hp => hC₁T (hsupp hC₁ hρ₁C hp))
    (fun x i u hu h => hP₀f x i u hu (hC₀T (by_contra fun hc => h (hρ₀C _ hc))))
    (fun x i u hu h => hP₁f x i u hu (hC₁T (by_contra fun hc => h (hρ₁C _ hc)))) hmid
  set Ω : ManifoldForm (𝓠 (n + 1 + 1)) A' (n + 1) :=
    formsInftyAlong (n + 1) hcs' (sndIncl hA') ω with hΩ_def
  have hΩ : ContMDiffForm (𝓠 (n + 1 + 1)) ∞ Ω := contMDiffForm_formsInftyAlong _ hchA' ω
  have hdγ : ContMDiffForm (𝓠 (n + 1 + 1)) ∞ (ManifoldForm.extDeriv γ) :=
    ContMDiffForm.extDeriv (hγ.of_le (by simp))
  have hΩext : IsExtendedBy (FaceFormData.d σ) Ω := by
    have h := isExtendedBy_formsInftyAlong_sndIncl hA' hcs' hchA' hX hdeg' ωN
    rw [hB, faceAlongData_formsD hcs' (sndIncl hA') hX hX' hdeg' hdegG hchA' N τN.2, ← hω] at h
    exact h
  have hγext : IsExtendedBy ((-1 : ℝ) • FaceFormData.d σ) (ManifoldForm.extDeriv γ) := by
    have h := hextγ.extDeriv (hγ.of_le (by simp))
    rwa [FaceFormData.d_smul] at h
  refine ⟨Ω + ManifoldForm.extDeriv γ, hΩ.add hdγ, ?_, fun x i u hu => ?_,
    fun x₀ a b hab hsub hρ => ?_, fun x₁ a b hab hsub hρ => ?_⟩
  · rw [extDeriv_add (hΩ.of_le (by simp)) (hdγ.of_le (by simp)),
      extDeriv_formsInftyAlong_sndIncl_eq_zero hA' hcs' hchA' ω hd,
      extDeriv_extDeriv (hγ.of_le (WithTop.coe_le_coe.2 le_top)), add_zero]
  · have hud := openFaceDomain_subset _ _ hu
    rw [faceRestriction_add, Pi.add_apply, Pi.add_apply, Pi.add_apply, hΩext x i hud,
      hγext x i hud, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Pi.zero_apply]
    module
  · refine ProductEnd.IsEndPullback.add ?_ ?_
    · exact isEndPullback_formsInftyAlong (Bd := BundledMPolyfold.of PX) hA' hab
        (fun z hz => hend₀ z (hsub hz)) x₀ hcs₀ hcs' hch₀ hchA' (subInclScMap hA₀) (sndIncl hA')
        (fun p hp => (endProj_val_of_mem (fun z hz => hend₀ z (hsub hz)) x₀ hp).symm) ω
    · exact (((hP₀e x₀ hab hsub).congr fun p hp => hγ0 p (hρ _ hp).1 (hρ _ hp).2).extDeriv
        (hγ.of_le (by simp)) (hγ₀.of_le (by simp)))
  · refine ProductEnd.IsEndPullback.add ?_ ?_
    · exact isEndPullback_formsInftyAlong (Bd := BundledMPolyfold.of PX) hA' hab
        (fun z hz => hend₁ z (hsub hz)) x₁ hcs₁ hcs' hch₁ hchA' (subInclScMap hA₁) (sndIncl hA')
        (fun p hp => (endProj_val_of_mem (fun z hz => hend₁ z (hsub hz)) x₁ hp).symm) ω
    · exact (((hP₁e x₁ hab hsub).congr fun p hp => hγ1 p (hρ _ hp).1 (hρ _ hp).2).extDeriv
        (hγ.of_le (by simp)) (hγ₁.of_le (by simp)))

end TwoEndsSucc

/-! ### Representatives of a closed relative form -/

section Rep

open BundledMPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  (hX : PX.IsTame)

/-- **A closed relative form of degree `0`** is the class of a form `ω ∈ Ω⁰(X^N)` with
`j^*ω = 0` on `bX^N` (`relD ω = (dω, j^*ω)`; an equality in the direct limit holds at some
level). -/
theorem exists_rep_of_mem_ker_relD_zero (c : LinearMap.ker (relD hX 0)) :
    ∃ (N : ℕ) (ω : (BundledMPolyfold.of PX).forms 0 N),
      (c : RelForms hX 0) = (BundledMPolyfold.of PX).formsInftyOf 0 N ω ∧
      formsPullback (bdryMap hX) 0 N ω = 0 ∧
      (BundledMPolyfold.of PX).formsInftyD 0 (c : RelForms hX 0) = 0 := by
  have hc : relDZero hX (c : RelForms hX 0) = 0 := LinearMap.mem_ker.1 c.2
  have h1 : (BundledMPolyfold.of PX).formsInftyD 0 (c : RelForms hX 0) = 0 :=
    congrArg Prod.fst hc
  have h2 : jStar hX 0 (c : RelForms hX 0) = 0 := congrArg Prod.snd hc
  obtain ⟨i, ω, hω⟩ := Module.DirectLimit.exists_of
    ((c : RelForms hX 0) : (BundledMPolyfold.of PX).formsInfty 0)
  have hω' : (c : RelForms hX 0) = (BundledMPolyfold.of PX).formsInftyOf 0 i ω := hω.symm
  rw [hω', jStar_of] at h2
  obtain ⟨j, hij, hj⟩ := Module.DirectLimit.of.zero_exact h2
  refine ⟨j, (BundledMPolyfold.of PX).formsMap 0 i j hij ω, ?_, ?_, h1⟩
  · rw [formsInftyOf_formsMap]; exact hω'
  · rw [formsPullback_formsMap]
    exact congrArg Subtype.val hj

/-- An equality `j^*[ω] = d[τ]` in `Ω^{m+1}_∞(∂X)` holds at some level `K`. -/
theorem exists_level_jStar_eq_d (m : ℕ) {i j : ℕ} (ω : (BundledMPolyfold.of PX).forms (m + 1) i)
    (τ : bForms hX m j)
    (h : jStar hX (m + 1) ((BundledMPolyfold.of PX).formsInftyOf (m + 1) i ω) =
      bFormsInftyD hX m (agreeDFormsInftyOf (bdryMap hX) m j τ)) :
    ∃ (K : ℕ) (hi : i ≤ K) (hj : j + 1 ≤ K),
      (bdry hX).formsMap (m + 1) i K hi (formsPullback (bdryMap hX) (m + 1) i ω) =
        (bdry hX).formsMap (m + 1) (j + 1) K hj ((bdry hX).formsD m j τ.1) := by
  rw [jStar_of, bFormsInftyD, agreeDFormsInftyD_of] at h
  have hiK : i ≤ max i (j + 1) := le_max_left _ _
  have hjK : j + 1 ≤ max i (j + 1) := le_max_right _ _
  rw [← agreeDFormsInftyOf_agreeDFormsMap (bdryMap hX) (m + 1) hiK,
    ← agreeDFormsInftyOf_agreeDFormsMap (bdryMap hX) (m + 1) hjK] at h
  obtain ⟨K', hKK', hK'⟩ := Module.DirectLimit.exists_eq_of_of_eq h
  have h3 : (bdry hX).formsMap (m + 1) (max i (j + 1)) K' hKK'
      ((bdry hX).formsMap (m + 1) i (max i (j + 1)) hiK
        (formsPullback (bdryMap hX) (m + 1) i ω)) =
    (bdry hX).formsMap (m + 1) (max i (j + 1)) K' hKK'
      ((bdry hX).formsMap (m + 1) (j + 1) (max i (j + 1)) hjK ((bdry hX).formsD m j τ.1)) :=
    congrArg Subtype.val hK'
  have e1 := LinearMap.congr_fun ((bdry hX).formsMap_comp (m + 1) hiK hKK')
    (formsPullback (bdryMap hX) (m + 1) i ω)
  have e2 := LinearMap.congr_fun ((bdry hX).formsMap_comp (m + 1) hjK hKK')
    ((bdry hX).formsD m j τ.1)
  exact ⟨K', hiK.trans hKK', hjK.trans hKK', e1.symm.trans (h3.trans e2)⟩

/-- From level `K` to the levels `K + 1` (for `ω`) and `K` (for `τ`): `j^*ω = dτ` on
`bX^{K+1}`. -/
theorem formsPullback_eq_formsD_of_level (m : ℕ) {i j K : ℕ}
    (ω : (BundledMPolyfold.of PX).forms (m + 1) i) (τ : bForms hX m j) (hi : i ≤ K)
    (hj : j + 1 ≤ K) (hi1 : i ≤ K + 1) (hj' : j ≤ K)
    (key : (bdry hX).formsMap (m + 1) i K hi (formsPullback (bdryMap hX) (m + 1) i ω) =
      (bdry hX).formsMap (m + 1) (j + 1) K hj ((bdry hX).formsD m j τ.1)) :
    formsPullback (bdryMap hX) (m + 1) (K + 1)
        ((BundledMPolyfold.of PX).formsMap (m + 1) i (K + 1) hi1 ω) =
      (bdry hX).formsD m K (agreeDFormsMap (bdryMap hX) m j K hj' τ).1 := by
  have hj1 : j + 1 ≤ K + 1 := Nat.succ_le_succ hj'
  have e3 := (LinearMap.congr_fun ((bdry hX).formsMap_succ (m + 1) hi hi1)
    (formsPullback (bdryMap hX) (m + 1) i ω)).trans (LinearMap.comp_apply _ _ _)
  have e4 := (LinearMap.congr_fun ((bdry hX).formsMap_succ (m + 1) hj hj1)
    ((bdry hX).formsD m j τ.1)).trans (LinearMap.comp_apply _ _ _)
  have s1 := formsPullback_formsMap (A := bdry hX) (B := BundledMPolyfold.of PX) (bdryMap hX)
    (m + 1) hi1 ω
  have s2 := congrArg ((bdry hX).formsStep (m + 1) K) key
  have s3 := formsD_formsMap (bdry hX) m hj' τ.1
  exact s1.trans (e3.trans (s2.trans (e4.symm.trans s3.symm)))

/-- **A closed relative form `(ω, τ)` of degree `m + 1`** has representatives
`ω ∈ Ω^{m+1}(X^{N+1})` and `τ ∈ Ω^m(∂X^N)` with `j^*ω = dτ` on `bX^{N+1}`
(`relD (ω, τ) = (dω, j^*ω − dτ)`; an equality in the direct limit holds at some level). -/
theorem exists_rep_of_mem_ker_relD_succ (m : ℕ) (c : LinearMap.ker (relD hX (m + 1))) :
    ∃ (N : ℕ) (ω : (BundledMPolyfold.of PX).forms (m + 1) (N + 1)) (τ : bForms hX m N),
      (c : RelForms hX (m + 1)).1 = (BundledMPolyfold.of PX).formsInftyOf (m + 1) (N + 1) ω ∧
      (c : RelForms hX (m + 1)).2 = agreeDFormsInftyOf (bdryMap hX) m N τ ∧
      formsPullback (bdryMap hX) (m + 1) (N + 1) ω = (bdry hX).formsD m N τ.1 ∧
      (BundledMPolyfold.of PX).formsInftyD (m + 1) (c : RelForms hX (m + 1)).1 = 0 := by
  have hc : relDSucc hX m (c : RelForms hX (m + 1)) = 0 := LinearMap.mem_ker.1 c.2
  have h1 : (BundledMPolyfold.of PX).formsInftyD (m + 1) (c : RelForms hX (m + 1)).1 = 0 :=
    congrArg Prod.fst hc
  have h2 : jStar hX (m + 1) (c : RelForms hX (m + 1)).1 =
      bFormsInftyD hX m (c : RelForms hX (m + 1)).2 := sub_eq_zero.1 (congrArg Prod.snd hc)
  obtain ⟨i, ω, hω⟩ := Module.DirectLimit.exists_of (c : RelForms hX (m + 1)).1
  have hω' : (c : RelForms hX (m + 1)).1 = (BundledMPolyfold.of PX).formsInftyOf (m + 1) i ω :=
    hω.symm
  obtain ⟨j, τ, hτ⟩ : ∃ j τ, (c : RelForms hX (m + 1)).2 = agreeDFormsInftyOf (bdryMap hX) m j τ :=
    agreeDFormsInfty_induction_on (bdryMap hX) m
      (C := fun z => ∃ j τ, z = agreeDFormsInftyOf (bdryMap hX) m j τ)
      (c : RelForms hX (m + 1)).2 fun j τ => ⟨j, τ, rfl⟩
  rw [hω', hτ] at h2
  obtain ⟨K, hi, hj, key⟩ := exists_level_jStar_eq_d hX m ω τ h2
  have hi1 : i ≤ K + 1 := Nat.le_succ_of_le hi
  have hj' : j ≤ K := (Nat.le_succ j).trans hj
  refine ⟨K, (BundledMPolyfold.of PX).formsMap (m + 1) i (K + 1) hi1 ω,
    agreeDFormsMap (bdryMap hX) m j K hj' τ, ?_, ?_,
    formsPullback_eq_formsD_of_level hX m ω τ hi hj hi1 hj' key, h1⟩
  · rw [formsInftyOf_formsMap]; exact hω'
  · rw [agreeDFormsInftyOf_agreeDFormsMap]; exact hτ

end Rep

end MPolyfold

/-! ### The cobordism `S_F`: its product parts and `d_{S_F} = d_{ℝ¹ × X}` -/

section Cobordism

open MPolyfold StrongBundle ManifoldForm BundledMPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))]
  (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
  {f₀ : X → Y} (hf₀ : B.IsScFredholmSectionTame f₀) {N₀ : B.One → ℝ} {U₀ : Set X} {s₀ : X → Y}
  (hs₀ : B.IsAdmissible f₀ N₀ U₀ s₀) (o₀ : SectionOrientation f₀ hf₀.toIsScFredholmSection)
  {f₁ : X → Y} (hf₁ : B.IsScFredholmSectionTame f₁) {N₁ : B.One → ℝ} {U₁ : Set X} {s₁ : X → Y}
  (hs₁ : B.IsAdmissible f₁ N₁ U₁ s₁) (o₁ : SectionOrientation f₁ hf₁.toIsScFredholmSection)
  {σ₁ : X → Y} {Ŝ : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
  (hC : B.IsCobordismData f₀ hf₀.isScSmooth.1 s₀ σ₁ Ŝ)
  (h₁ : sectionAdd P f₀ σ₁ = sectionAdd P f₁ s₁) (k : ℕ)

include hs₀ hC in
/-- **Over `t < 1/8`, `S_F^{k+1}` is the product with `S₀ = S_{f₀+s₀} ∩ V_k`**
(`cobPart_end_left` for every `t < 1/8`: the slices of `Ŝ` are `s₀` for `t ≤ 1/8`). -/
theorem cobPart_iff_left (z : (Fin 1 → ℝ) × X) (hz : z.1 0 ∈ Iio (1 / 8 : ℝ)) :
    z ∈ cobPart hf₀ Ŝ k ↔ z.2 ∈ B.solPart f₀ s₀ k :=
  solutionSet_end_iff (a := z.1 0 - 1) (b := 1 / 8)
    ((isSection_pullbackLift _).sectionAdd hC.isSection) (hC.slice_left_Ioo le_rfl)
    (hC.hVend_left hf₀ le_rfl (mem_solIndexNbhd_iff_isLinOfIndex hf₀.toIsScFredholmSection
      hs₀.isScPlusSection k) (cobIndexNbhd_iff hf₀ hC k)) z ⟨by linarith, hz⟩

include hf₁ hs₁ hC h₁ in
/-- **Over `t > 7/8`, `S_F^{k+1}` is the product with `S₁ = S_{f₁+s₁} ∩ V_k`**. -/
theorem cobPart_iff_right (z : (Fin 1 → ℝ) × X) (hz : z.1 0 ∈ Ioi (7 / 8 : ℝ)) :
    z ∈ cobPart hf₀ Ŝ k ↔ z.2 ∈ B.solPart f₁ s₁ k := by
  have hVk : ∀ x ∈ solutionSet P (sectionAdd P f₀ σ₁),
      x ∈ B.solIndexNbhd f₁ s₁ k ↔ B.IsLinOfIndex (sectionAdd P f₀ σ₁) x k := by
    rw [h₁]
    exact mem_solIndexNbhd_iff_isLinOfIndex hf₁.toIsScFredholmSection hs₁.isScPlusSection k
  have := solutionSet_end_iff (a := 7 / 8) (b := z.1 0 + 1)
    ((isSection_pullbackLift _).sectionAdd hC.isSection)
    (hC.slice_right_Ioo le_rfl) (hC.hVend_right hf₀ le_rfl hVk (cobIndexNbhd_iff hf₀ hC k)) z
    ⟨hz, by linarith⟩
  rwa [h₁] at this

include hX hC in
/-- `S_F^{k+1}` is in general position at each of its points (Definition 4.2.10). -/
theorem isGeneralPositionAt_cobPart :
    ∀ y ∈ cobPart hf₀ Ŝ k,
      ((rnPolyfold 1).prod PX).IsGeneralPositionAt (cobPart hf₀ Ŝ k) y := by
  have hft := hC.isScFredholmSectionTame_homotopySection hf₀
  have hV := isOpen_cobIndexNbhd hf₀ hC k
  intro y hy
  obtain ⟨W, hWo, hyW, hWA, hW⟩ :=
    exists_isOpen_isGeneralPositionGerm (prod_rn_isTame hX) hft hy.1 (hC.gp y hy.1)
  refine MPolyfold.IsGeneralPositionAt.congr_nhds hWA (isSubmanifoldOfDim_cobPart hf₀ hC k).1
    (hWo.inter hV) ⟨hyW, hy.2⟩ ?_ (hW y hyW hy.1).2.2
  ext w
  simp only [cobPart, mem_inter_iff]
  tauto

include hX hC in
/-- **`d_{S_F} = d_{ℝ¹ × X}`** on `S_F^{k+1}` (Theorem 4.2.11 (2), 2021 p. 190). -/
theorem degIndex_cobPart (a : ↥(cobPart hf₀ Ŝ k)) :
    (subPolyfold (isSubMPolyfold_cobPart hf₀ hC k)).degIndex a =
      ((rnPolyfold 1).prod PX).degIndex a := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, W, -, haW, -, -, -, h2, -⟩ :=
    MPolyfold.theorem_4_2_11_preprint (prod_rn_isTame hX) (isSubmanifoldOfDim_cobPart hf₀ hC k).1
      (isGeneralPositionAt_cobPart hX hf₀ hC k a a.2)
  exact h2 a haW

/-! ### The relative form on `S_F`, on the inner ends -/

/-- **The inner left end `(0, 1/16) × S₀` of `S_F^{k+1}`** as a `ProductEnd`: the part of the
left end `cobEndLeft` over `(0, 1/16)`. -/
abbrev cobEndLeftIn (x₀ : ↥(B.solPart f₀ s₀ k)) :
    letI := solPartChartedSpace hX hf₀ hs₀ k
    letI := cobChartedSpace hX hf₀ hC k
    ProductEnd k ↥(B.solPart f₀ s₀ k) ↥(cobPart hf₀ Ŝ k) 0 (1 / 16) :=
  letI := solPartChartedSpace hX hf₀ hs₀ k
  letI := cobChartedSpace hX hf₀ hC k
  endOver (isSubMPolyfold_cobPart hf₀ hC k) (T := Iio (1 / 8 : ℝ))
    (cobPart_iff_left hf₀ hs₀ hC k) x₀ (hasCornerStructureOfDim_solPart hX hf₀ hs₀ k)
    (hasCornerStructureOfDim_cobPart hX hf₀ hC k) rfl rfl (by norm_num : (0 : ℝ) < 1 / 16)
    (fun s hs => (hs.2.trans (by norm_num) : s < 1 / 8))

/-- **The inner right end `(15/16, 1) × S₁` of `S_F^{k+1}`** as a `ProductEnd`: the part of the
right end `cobEndRight` over `(15/16, 1)`. -/
abbrev cobEndRightIn (x₀ : ↥(B.solPart f₁ s₁ k)) :
    letI := solPartChartedSpace hX hf₁ hs₁ k
    letI := cobChartedSpace hX hf₀ hC k
    ProductEnd k ↥(B.solPart f₁ s₁ k) ↥(cobPart hf₀ Ŝ k) (15 / 16) 1 :=
  letI := solPartChartedSpace hX hf₁ hs₁ k
  letI := cobChartedSpace hX hf₀ hC k
  endOver (isSubMPolyfold_cobPart hf₀ hC k) (T := Ioi (7 / 8 : ℝ))
    (cobPart_iff_right hf₀ hf₁ hs₁ hC h₁ k) x₀ (hasCornerStructureOfDim_solPart hX hf₁ hs₁ k)
    (hasCornerStructureOfDim_cobPart hX hf₀ hC k) rfl rfl (by norm_num : (15 / 16 : ℝ) < 1)
    (fun s hs => ((by norm_num : (7 / 8 : ℝ) < 15 / 16).trans hs.1 : 7 / 8 < s))

/-- **The relative form on the cobordism, on the inner ends** (the form `p₁^*ω − dβ` on `S_F` of
2021 p. 278, with `j^*β = p₁^*τ` on `∂S_F`): `CobordismRelativeForms` of
`InvariantCobordism2021`, with the product ends `(0, 1/8) × S₀` and `(7/8, 1) × S₁` replaced by
the inner ends `(0, 1/16) × S₀` and `(15/16, 1) × S₁`.  The cobordism data give the product
structure of `S_F` for `t ≤ 1/8` and `t ≥ 7/8` only, so a form on `S_F` equal to a pull-back on
all of `(0, 1/8) × S₀` would have to be continued across `t = 1/8` without a product structure;
on the inner ends the cut-offs in `t` have room. -/
def CobordismRelativeFormsInner : Prop :=
  letI := solPartChartedSpace hX hf₀ hs₀ k
  letI := solPartChartedSpace hX hf₁ hs₁ k
  letI := cobChartedSpace hX hf₀ hC k
  ∀ (c : LinearMap.ker (relD hX k)) (a₀ : ManifoldForm (𝓠 k) ↥(B.solPart f₀ s₀ k) k)
    (a₁ : ManifoldForm (𝓠 k) ↥(B.solPart f₁ s₁ k) k),
    IsPsiIntegrand hX hf₀ hs₀ k c a₀ → IsPsiIntegrand hX hf₁ hs₁ k c a₁ →
    ∃ F : ManifoldForm (𝓠 (k + 1)) ↥(cobPart hf₀ Ŝ k) k,
      ManifoldForm.ContMDiffForm (𝓠 (k + 1)) ∞ F ∧ ManifoldForm.extDeriv F = 0 ∧
      (∀ x i, EqOn (faceRestriction F x i) 0
        (openFaceDomain (chartAt (EuclideanQuadrant (k + 1)) x) i)) ∧
      (∀ x₀ : ↥(B.solPart f₀ s₀ k), (cobEndLeftIn hX hf₀ hs₀ hC k x₀).IsEndPullback F a₀) ∧
      ∀ x₀ : ↥(B.solPart f₁ s₁ k), (cobEndRightIn hX hf₀ hf₁ hs₁ hC h₁ k x₀).IsEndPullback F a₁

/-- **The relative form on the cobordism in degree `0`**: `F = (p₁^*ω)|_{S_F}`, a closed
function on the `1`-dimensional `S_F^1` which vanishes at its boundary points (`j^*ω = 0`). -/
theorem cobordismRelativeFormsInner_zero :
    CobordismRelativeFormsInner hX hf₀ hs₀ hf₁ hs₁ hC h₁ 0 := by
  intro c a₀ a₁ ha₀ ha₁
  let := solPartChartedSpace hX hf₀ hs₀ 0
  let := solPartChartedSpace hX hf₁ hs₁ 0
  let := cobChartedSpace hX hf₀ hC 0
  obtain ⟨N, ωN, hω, hB, hd⟩ := exists_rep_of_mem_ker_relD_zero hX c
  refine ⟨formsInftyAlong 0 (hasCornerStructureOfDim_cobPart hX hf₀ hC 0)
    (sndIncl (isSubMPolyfold_cobPart hf₀ hC 0)) (c : RelForms hX 0),
    contMDiffForm_formsInftyAlong _ rfl _,
    extDeriv_formsInftyAlong_sndIncl_eq_zero (isSubMPolyfold_cobPart hf₀ hC 0)
      (hasCornerStructureOfDim_cobPart hX hf₀ hC 0) rfl _ hd, fun x i u hu => ?_,
    fun x₀ => ?_, fun x₀ => ?_⟩
  · have h := isExtendedBy_formsInftyAlong_sndIncl (isSubMPolyfold_cobPart hf₀ hC 0)
      (hasCornerStructureOfDim_cobPart hX hf₀ hC 0) rfl hX (degIndex_cobPart hX hf₀ hC 0) ωN x i
      (openFaceDomain_subset _ _ hu)
    rw [hB, faceAlongData_zero, ← hω] at h
    exact h
  · have ha : a₀ = formsInftyRestrict 0 (hasCornerStructureOfDim_solPart hX hf₀ hs₀ 0)
        (c : RelForms hX 0) := ha₀
    have hend : ∀ z : (Fin 1 → ℝ) × X, z.1 0 ∈ Ioo (0 : ℝ) (1 / 16) →
        (z ∈ cobPart hf₀ Ŝ 0 ↔ z.2 ∈ B.solPart f₀ s₀ 0) :=
      fun z hz => cobPart_iff_left hf₀ hs₀ hC 0 z (hz.2.trans (by norm_num))
    rw [ha]
    exact isEndPullback_formsInftyAlong (Bd := BundledMPolyfold.of PX)
      (isSubMPolyfold_cobPart hf₀ hC 0) (by norm_num : (0 : ℝ) < 1 / 16) hend x₀
      (hasCornerStructureOfDim_solPart hX hf₀ hs₀ 0)
      (hasCornerStructureOfDim_cobPart hX hf₀ hC 0) rfl rfl (subInclScMap _)
      (sndIncl (isSubMPolyfold_cobPart hf₀ hC 0))
      (fun p hp => (endProj_val_of_mem hend x₀ hp).symm) (c : RelForms hX 0)
  · have ha : a₁ = formsInftyRestrict 0 (hasCornerStructureOfDim_solPart hX hf₁ hs₁ 0)
        (c : RelForms hX 0) := ha₁
    have hend : ∀ z : (Fin 1 → ℝ) × X, z.1 0 ∈ Ioo (15 / 16 : ℝ) 1 →
        (z ∈ cobPart hf₀ Ŝ 0 ↔ z.2 ∈ B.solPart f₁ s₁ 0) :=
      fun z hz => cobPart_iff_right hf₀ hf₁ hs₁ hC h₁ 0 z
        ((by norm_num : (7 / 8 : ℝ) < 15 / 16).trans hz.1)
    rw [ha]
    exact isEndPullback_formsInftyAlong (Bd := BundledMPolyfold.of PX)
      (isSubMPolyfold_cobPart hf₀ hC 0) (by norm_num : (15 / 16 : ℝ) < 1) hend x₀
      (hasCornerStructureOfDim_solPart hX hf₁ hs₁ 0)
      (hasCornerStructureOfDim_cobPart hX hf₀ hC 0) rfl rfl (subInclScMap _)
      (sndIncl (isSubMPolyfold_cobPart hf₀ hC 0))
      (fun p hp => (endProj_val_of_mem hend x₀ hp).symm) (c : RelForms hX 0)

/-- **The relative form on the cobordism in degree `m + 1`**: `F = (p₁^*ω)|_{S_F} + dγ_F`, with
`γ_F` an extension of `−(p₁^*τ)|_{∂S_F}` equal to `p₁^*γ_i` on the inner ends
(`exists_closed_form_of_ends`, with the cut-offs `ρ₀ = 1 − cutRise (1/16) (1/8)` and
`ρ₁ = cutRise (7/8) (15/16)`). -/
theorem cobordismRelativeFormsInner_succ (m : ℕ) :
    CobordismRelativeFormsInner hX hf₀ hs₀ hf₁ hs₁ hC h₁ (m + 1) := by
  intro c a₀ a₁ ha₀ ha₁
  obtain ⟨γ₀, hγ₀, -, hext₀, rfl⟩ := ha₀
  obtain ⟨γ₁, hγ₁, -, hext₁, rfl⟩ := ha₁
  obtain ⟨N, ωN, τN, hω, hτ, hB, hd⟩ := exists_rep_of_mem_ker_relD_succ hX m c
  let := solPartChartedSpace hX hf₀ hs₀ (m + 1)
  let := solPartChartedSpace hX hf₁ hs₁ (m + 1)
  let := cobChartedSpace hX hf₀ hC (m + 1)
  have := sigmaCompactSpace_cobPart hf₀ hC (m + 1)
  have hext₀' : IsExtendedBy ((-1 : ℝ) • faceAlongData
      (hasCornerStructureOfDim_solPart hX hf₀ hs₀ (m + 1)) (subInclScMap _) hX N τN.1) γ₀ := by
    have h := hext₀
    rw [hτ, solFaceForm_of] at h
    exact h
  have hext₁' : IsExtendedBy ((-1 : ℝ) • faceAlongData
      (hasCornerStructureOfDim_solPart hX hf₁ hs₁ (m + 1)) (subInclScMap _) hX N τN.1) γ₁ := by
    have h := hext₁
    rw [hτ, solFaceForm_of] at h
    exact h
  have h16 : (1 / 16 : ℝ) < 1 / 8 := by norm_num
  have h78 : (7 / 8 : ℝ) < 15 / 16 := by norm_num
  obtain ⟨F, hF, hF0, hFf, hFL, hFR⟩ := exists_closed_form_of_ends
    (isSubMPolyfold_cobPart hf₀ hC (m + 1)) (hasCornerStructureOfDim_cobPart hX hf₀ hC (m + 1))
    rfl hX (degIndex_cobPart hX hf₀ hC (m + 1)) (isCompact_cobSlab hf₀ hC (m + 1))
    (hasCornerStructureOfDim_solPart hX hf₀ hs₀ (m + 1)) rfl (degIndex_solPart hX hf₀ hs₀ (m + 1))
    isOpen_Iio (cobPart_iff_left hf₀ hs₀ hC (m + 1))
    (hasCornerStructureOfDim_solPart hX hf₁ hs₁ (m + 1)) rfl (degIndex_solPart hX hf₁ hs₁ (m + 1))
    isOpen_Ioi (cobPart_iff_right hf₀ hf₁ hs₁ hC h₁ (m + 1))
    (c : RelForms hX (m + 1)).1 ωN τN hω hB hd hγ₀ hext₀' hγ₁ hext₁'
    (ρ₀ := fun s => 1 - cutRise (1 / 16) (1 / 8) s) (ρ₁ := cutRise (7 / 8) (15 / 16))
    (contDiff_const.sub (contDiff_cutRise _ _)) (contDiff_cutRise _ _)
    (C₀ := Iic (5 / 48)) (C₁ := Ici (43 / 48)) isClosed_Iic
    (fun s (hs : s ≤ 5 / 48) => (lt_of_le_of_lt hs (by norm_num) : s < 1 / 8))
    (fun s hs => by
      have hs' : (5 / 48 : ℝ) < s := not_le.1 hs
      rw [cutRise_eq_one h16 (by linarith), sub_self])
    isClosed_Ici
    (fun s (hs : (43 / 48 : ℝ) ≤ s) => (lt_of_lt_of_le (by norm_num) hs : 7 / 8 < s))
    (fun s hs => by
      have hs' : s < 43 / 48 := not_le.1 hs
      exact cutRise_eq_zero h78 (by linarith))
    (l := 0) (u := 1) (fun s hs => by
      rcases not_and_or.1 hs with h | h
      · have h' : s < 0 := not_le.1 h
        rw [cutRise_eq_zero h16 (by linarith), cutRise_eq_zero h78 (by linarith)]
        norm_num
      · have h' : 1 < s := not_le.1 h
        rw [cutRise_eq_one h16 (by linarith), cutRise_eq_one h78 (by linarith)]
        norm_num)
  refine ⟨F, hF, hF0, hFf, fun x₀ => hFL x₀ _ _ fun s hs => ⟨?_, ?_⟩,
    fun x₀ => hFR x₀ _ _ fun s hs => ⟨?_, ?_⟩⟩
  · rw [cutRise_eq_zero h16 (by linarith [hs.2]), sub_zero]
  · exact cutRise_eq_zero h78 (by linarith [hs.2])
  · exact cutRise_eq_one h78 (by linarith [hs.1])
  · rw [cutRise_eq_one h16 (by linarith [hs.1]), sub_self]

/-- **The relative forms on the cobordisms of the proof of 2021 Theorem 6.7.1** (p. 278;
preprint Theorem 6.43), on the inner ends: for every closed relative form `c = (ω, τ)` and
integrands `a₀`, `a₁` of `c`, a closed `C^∞` form on `S_F^{k+1}` with vanishing face restriction
reading as `a₀`, `a₁` on the inner ends.  No hypothesis beyond the cobordism data. -/
theorem cobordismRelativeFormsInner : CobordismRelativeFormsInner hX hf₀ hs₀ hf₁ hs₁ hC h₁ k := by
  cases k with
  | zero => exact cobordismRelativeFormsInner_zero hX hf₀ hs₀ hf₁ hs₁ hC h₁
  | succ m => exact cobordismRelativeFormsInner_succ hX hf₀ hs₀ hf₁ hs₁ hC h₁ m

/-! ### The cobordism identity for `Ψ`, from the orientation of the cobordism alone -/

/-- The inner left end is a cut end (`HasCutEnd`): the product orientation is that of the left
end `cobEndLeft` (`IsEndProductOrientation.of_subEnd`). -/
theorem hasCutEnd_leftIn :
    letI := solPartChartedSpace hX hf₀ hs₀ k
    letI := cobChartedSpace hX hf₀ hC k
    ∀ {oM : TangentOrientation (𝓠 (k + 1)) ↥(cobPart hf₀ Ŝ k) (k + 1)}
      {F : ManifoldForm (𝓠 (k + 1)) ↥(cobPart hf₀ Ŝ k) k}
      {a₀ : ManifoldForm (𝓠 k) ↥(B.solPart f₀ s₀ k) k},
      (∀ x₀ : ↥(B.solPart f₀ s₀ k),
        (cobEndLeft hX hf₀ hs₀ hC k x₀).IsEndProductOrientation oM (solPartOr hX hf₀ hs₀ o₀ k)) →
      (∀ x₀ : ↥(B.solPart f₀ s₀ k), (cobEndLeftIn hX hf₀ hs₀ hC k x₀).IsEndPullback F a₀) →
      HasCutEnd 0 (1 / 16) (cobTime hf₀ Ŝ k) oM (solPartOr hX hf₀ hs₀ o₀ k) F a₀ := by
  intro oM F a₀ hor hpull
  let := solPartChartedSpace hX hf₀ hs₀ k
  let := cobChartedSpace hX hf₀ hC k
  rcases isEmpty_or_nonempty ↥(B.solPart f₀ s₀ k) with hN | ⟨⟨x₀⟩⟩
  · exact Or.inl ⟨hN, fun p hp => hN.false
      ⟨_, (cobPart_iff_left hf₀ hs₀ hC k p.1 (hp.2.trans (by norm_num))).1 p.2⟩⟩
  · exact Or.inr ⟨cobEndLeftIn hX hf₀ hs₀ hC k x₀,
      (hor x₀).of_subEnd (fun p hp => ⟨hp.1, hp.2.trans (by norm_num)⟩) (fun _ _ => rfl),
      hpull x₀, fun _ _ => rfl, fun _ hp => hp⟩

/-- The inner right end is a cut end. -/
theorem hasCutEnd_rightIn :
    letI := solPartChartedSpace hX hf₁ hs₁ k
    letI := cobChartedSpace hX hf₀ hC k
    ∀ {oM : TangentOrientation (𝓠 (k + 1)) ↥(cobPart hf₀ Ŝ k) (k + 1)}
      {F : ManifoldForm (𝓠 (k + 1)) ↥(cobPart hf₀ Ŝ k) k}
      {a₁ : ManifoldForm (𝓠 k) ↥(B.solPart f₁ s₁ k) k},
      (∀ x₀ : ↥(B.solPart f₁ s₁ k),
        (cobEndRight hX hf₀ hf₁ hs₁ hC h₁ k x₀).IsEndProductOrientation oM
          (solPartOr hX hf₁ hs₁ o₁ k)) →
      (∀ x₀ : ↥(B.solPart f₁ s₁ k),
        (cobEndRightIn hX hf₀ hf₁ hs₁ hC h₁ k x₀).IsEndPullback F a₁) →
      HasCutEnd (15 / 16) 1 (cobTime hf₀ Ŝ k) oM (solPartOr hX hf₁ hs₁ o₁ k) F a₁ := by
  intro oM F a₁ hor hpull
  let := solPartChartedSpace hX hf₁ hs₁ k
  let := cobChartedSpace hX hf₀ hC k
  rcases isEmpty_or_nonempty ↥(B.solPart f₁ s₁ k) with hN | ⟨⟨x₀⟩⟩
  · exact Or.inl ⟨hN, fun p hp => hN.false ⟨_, (cobPart_iff_right hf₀ hf₁ hs₁ hC h₁ k p.1
      ((by norm_num : (7 / 8 : ℝ) < 15 / 16).trans hp.1)).1 p.2⟩⟩
  · exact Or.inr ⟨cobEndRightIn hX hf₀ hf₁ hs₁ hC h₁ k x₀,
      (hor x₀).of_subEnd
        (fun p hp => ⟨(by norm_num : (7 / 8 : ℝ) < 15 / 16).trans hp.1, hp.2⟩) (fun _ _ => rfl),
      hpull x₀, fun _ _ => rfl, fun _ hp => hp⟩

include hbump in
/-- **The cobordism identity for `Ψ`, from the orientation of the cobordism** (the proof of 2021
Theorem 6.7.1 (1), p. 277–279, and the "same homotopy argument" of (2), p. 279; preprint
Theorem 6.43): `psiAt_eq_of_cobordism` of `InvariantCobordism2021` without its hypothesis
`CobordismRelativeForms`.  The relative form on `S_F` is `cobordismRelativeFormsInner`; the
cut-off argument `integral_eq_of_cutCobordism` is run on the inner ends `(0, 1/16) × S₀` and
`(15/16, 1) × S₁`, on which the orientation of `S_F` is still the product orientation. -/
theorem psiAt_eq_of_cobordism_of_orientation
    (hOr : CobordismOrientation hX hf₀ hs₀ o₀ hf₁ hs₁ o₁ hC h₁ k) :
    psiAt hX hbump hf₀ hs₀ o₀ k = psiAt hX hbump hf₁ hs₁ o₁ k := by
  have hS₀ := hC.isCompact_solutionSet_left
  have hS₁ : IsCompact (solutionSet P (sectionAdd P f₁ s₁)) := h₁ ▸ hC.isCompact_solutionSet_right
  obtain ⟨oM, hoM, horL, horR⟩ := hOr
  refine Submodule.linearMap_qext _ (LinearMap.ext fun c => ?_)
  simp only [LinearMap.comp_apply]
  obtain ⟨a₀, ha₀⟩ := exists_isPsiIntegrand hX hf₀ hs₀ hS₀ k c
  obtain ⟨a₁, ha₁⟩ := exists_isPsiIntegrand hX hf₁ hs₁ hS₁ k c
  obtain ⟨F, hF, hF0, hface, hpullL, hpullR⟩ :=
    cobordismRelativeFormsInner hX hf₀ hs₀ hf₁ hs₁ hC h₁ k c a₀ a₁ ha₀ ha₁
  let := solPartChartedSpace hX hf₀ hs₀ k
  let := solPartChartedSpace hX hf₁ hs₁ k
  let := cobChartedSpace hX hf₀ hC k
  have := isManifold_solPart hX hf₀ hs₀ k
  have := isManifold_solPart hX hf₁ hs₁ k
  have := isManifold_cobPart hX hf₀ hC k
  have := sigmaCompactSpace_cobPart hf₀ hC k
  have := isCompact_iff_compactSpace.1 (isCompact_solPart hf₀ hs₀.isScPlusSection hs₀.gp hS₀ k)
  have := isCompact_iff_compactSpace.1 (isCompact_solPart hf₁ hs₁.isScPlusSection hs₁.gp hS₁ k)
  change psiAt hX hbump hf₀ hs₀ o₀ k (relDeRhamMk hX k c) =
    psiAt hX hbump hf₁ hs₁ o₁ k (relDeRhamMk hX k c)
  rw [ha₀.psiAt_eq hX hbump hf₀ hs₀ o₀ hS₀, ha₁.psiAt_eq hX hbump hf₁ hs₁ o₁ hS₁]
  exact integral_eq_of_cutCobordism (by norm_num) (by norm_num) hoM
    (isContinuous_solPartOr hX hbump hf₀ hs₀ o₀ k) (isContinuous_solPartOr hX hbump hf₁ hs₁ o₁ k)
    (contMDiff_cobTime hX hf₀ hC k) (isCompact_cobSlab hf₀ hC k) hF hF0 hface
    ((ha₀.contMDiffForm hX hf₀ hs₀).of_le (by simp)) isClosed_closure.isCompact
    ((ha₁.contMDiffForm hX hf₁ hs₁).of_le (by simp)) isClosed_closure.isCompact
    (hasCutEnd_leftIn hX hf₀ hs₀ o₀ hC k horL hpullL)
    (hasCutEnd_rightIn hX hf₀ hf₁ hs₁ o₁ hC h₁ k horR hpullR)

end Cobordism

/-! ### Theorem 6.7.1 from the orientation of the cobordisms alone -/

section Steps

open MPolyfold StrongBundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)

/-- **(A) of the proof of 2021 Theorem 6.7.1** (p. 277–279), from the orientation of the
cobordisms: `Ψ_{s₀} = Ψ_{s₁}` for two sections admissible for one `(N, U)`
(`PsiIndepAdmissible`); `psiAt_eq_of_admissible_hyp` without `CobordismRelativeFormsHyp`. -/
theorem psiAt_eq_of_admissible_of_orientation (hOr : CobordismOrientationHyp B hX) :
    PsiIndepAdmissible B hX hbump := by
  intro f hf _ o N hN U hU hSU hmar s₀ s₁ hs₀ hs₁ k
  have := paracompactSpace_rn_prod PX 1
  have := paracompactSpace_rn_pullback B 1
  obtain ⟨hOrA, -⟩ := hOr
  obtain ⟨Ŝ, hC⟩ := exists_isCobordismData hX hbump hf hN hU hSU (hmar 2 two_pos) hs₀.mem
    hs₁.mem hs₀.gp hs₁.gp
  exact psiAt_eq_of_cobordism_of_orientation hX hbump hf hs₀ o hf hs₁ o hC rfl k
    (hOrA f hf o N U s₀ s₁ hs₀ hs₁ Ŝ hC k)

/-- **(B) of the proof of 2021 Theorem 6.7.1** (p. 279, "the same homotopy argument"), from the
orientation of the cobordisms: `Ψ_{s₀}(f₀, o₀) = Ψ_{s₁}(f₁, o₁)` along a proper oriented homotopy
(`PsiIndepHomotopy`); `psiAt_eq_of_homotopy_hyp` without `CobordismRelativeFormsHyp`. -/
theorem psiAt_eq_of_homotopy_of_orientation (hOr : CobordismOrientationHyp B hX) :
    PsiIndepHomotopy B hX hbump := by
  intro f₀ hf₀ o₀ S hf₁ o₁ hHB N₀ hN₀ U₀ hU₀ hSU₀ hmar₀ N₁ hN₁ U₁ hU₁ hSU₁ hmar₁ s₀ s₁ hs₀ hs₁ k
  have := paracompactSpace_rn_prod PX 1
  have := paracompactSpace_rn_pullback B 1
  have hA := psiAt_eq_of_admissible_of_orientation hX hbump hOr
  obtain ⟨-, hOrB⟩ := hOr
  obtain ⟨hH, -⟩ := id hHB
  have hP₀ : B.IsProper f₀ := hH.isProper_zero
  have hP₁ : B.IsProper (sectionAdd P f₀ (pullbackSlice S 1)) := hH.isProper_one
  obtain ⟨V₁, hV₁, hSV₁, hmarV₁, -⟩ :=
    exists_isAdmissible_nbhd hX hbump hf₁ hH.isCompact_solutionSet_one hN₀
  obtain ⟨s₀', s₁', Ŝ, h₀', hgp₀', h₁', hgp₁', hC⟩ :=
    exists_homotopy_cobordism_data hX hbump hH hN₀ hU₀ hSU₀ hV₁ hSV₁
  have hs₀' : B.IsAdmissible f₀ N₀ U₀ s₀' := ⟨h₀', hgp₀'⟩
  have hs₁' : B.IsAdmissible (sectionAdd P f₀ (pullbackSlice S 1)) N₀ V₁ s₁' := ⟨h₁', hgp₁'⟩
  have h₁ : sectionAdd P f₀ (sectionAdd P (pullbackSlice S 1) s₁') =
      sectionAdd P (sectionAdd P f₀ (pullbackSlice S 1)) s₁' :=
    (sectionAdd_assoc hf₀.isScSmooth.1 hH.slice_one.1 hs₁'.isScPlusSection.1).symm
  calc psiAt hX hbump hf₀ hs₀ o₀ k = psiAt hX hbump hf₀ hs₀' o₀ k :=
        hA f₀ hf₀ hP₀ o₀ N₀ hN₀ U₀ hU₀ hSU₀ hmar₀ s₀ s₀' hs₀ hs₀' k
    _ = psiAt hX hbump hf₁ hs₁' o₁ k :=
        psiAt_eq_of_cobordism_of_orientation hX hbump hf₀ hs₀' o₀ hf₁ hs₁' o₁ hC h₁ k
          (hOrB f₀ hf₀ o₀ S hf₁ o₁ hHB N₀ U₀ s₀' hs₀' N₀ V₁ s₁' hs₁' Ŝ hC h₁ k)
    _ = psiInvariant hX hbump hf₁ hP₁ o₁ k :=
        (psiInvariant_eq_psiAt hX hbump hA hf₁ hP₁ o₁ hN₀ hV₁ hSV₁ hmarV₁ hs₁' k).symm
    _ = psiAt hX hbump hf₁ hs₁ o₁ k :=
        psiInvariant_eq_psiAt hX hbump hA hf₁ hP₁ o₁ hN₁ hU₁ hSU₁ hmar₁ hs₁ k

end Steps

section Theorem

open MPolyfold StrongBundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

/-- **2021 Theorem 6.7.1** (p. 277; preprint Theorem 6.43), from the orientation of the
cobordisms alone.  The statement is that of `theorem_6_7_1_hyp`; its second hypothesis
`CobordismRelativeFormsHyp` (the relative form `p₁^*ω − dβ` on `S_F`) is no longer needed:
the form is built in `cobordismRelativeFormsInner`.  The remaining hypothesis
`CobordismOrientationHyp` (the orientation of the cobordism `S_F`, Remark 6.6.19) is proved as
`cobordismOrientationHyp` (`CobordismOrientationEnds2021d`); Theorem 6.7.1 without hypotheses on
the cobordism is `theorem_6_7_1` (`Theorem671Final2021`). -/
theorem theorem_6_7_1_of_orientation (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hOr : CobordismOrientationHyp B hX) :
    ∃ Ψ : ∀ (f : X → Y) (hf : B.IsScFredholmSectionTame f), B.IsProper f →
        SectionOrientation f hf.toIsScFredholmSection → ∀ k : ℕ, relDeRham hX k →ₗ[ℝ] ℝ,
      (∀ (f : X → Y) (hf : B.IsScFredholmSectionTame f) (hP : B.IsProper f)
          (o : SectionOrientation f hf.toIsScFredholmSection) (N : B.One → ℝ), B.IsAuxNorm N →
        (∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
          ∀ C : ℝ, 0 < C → IsCompact (closure {x ∈ U | B.AuxLe N (f x) C})) ∧
        ∀ U : Set X, IsOpen U → solutionSet P f ⊆ U →
          (∀ C : ℝ, 0 < C → IsCompact (closure {x ∈ U | B.AuxLe N (f x) C})) →
          (∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s))) ∧
          (∃ s, B.IsAdmissible f N U s) ∧
          ∀ (s : X → Y) (hs : B.IsAdmissible f N U s),
            IsCompact (solutionSet P (sectionAdd P f s)) ∧
            solutionSet P (sectionAdd P f s) = ⋃ k : ℕ, B.solPart f s k ∧
            ∀ k : ℕ, IsCompact (B.solPart f s k) ∧ SolPartIsOrientedManifold hX hf hs o k ∧
              ∀ c : LinearMap.ker (relD hX k),
                Ψ f hf hP o k (relDeRhamMk hX k c) =
                  solIntegral hX hbump hf hs o k c - solBoundaryIntegral hX hbump hf hs o k c) ∧
      ∀ (f₀ : X → Y) (hf₀ : B.IsScFredholmSectionTame f₀) (hP₀ : B.IsProper f₀)
        (o₀ : SectionOrientation f₀ hf₀.toIsScFredholmSection)
        (S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))
        (hf₁ : B.IsScFredholmSectionTame (sectionAdd P f₀ (pullbackSlice S 1)))
        (hP₁ : B.IsProper (sectionAdd P f₀ (pullbackSlice S 1)))
        (o₁ : SectionOrientation (sectionAdd P f₀ (pullbackSlice S 1)) hf₁.toIsScFredholmSection),
        IsProperOrientedHomotopyBetween hf₀ o₀ S o₁ →
          ∀ k : ℕ, Ψ f₀ hf₀ hP₀ o₀ k = Ψ _ hf₁ hP₁ o₁ k :=
  theorem_6_7_1_of_indep hX hbump (psiAt_eq_of_admissible_of_orientation hX hbump hOr)
    (psiAt_eq_of_homotopy_of_orientation hX hbump hOr)

/-- **2021 p. 279, the case `∂X = ∅` of Theorem 6.7.1** (2017: after Theorem 6.4; preprint
p. 233), from the orientation of the cobordisms alone: the statement of
`theorem_6_7_1_noBoundary_hyp` without `CobordismRelativeFormsHyp`. -/
theorem theorem_6_7_1_noBoundary_of_orientation (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hbd : PX.IsWithoutBoundary) (hOr : CobordismOrientationHyp B hX) :
    ∃ Φ : ∀ (f : X → Y) (hf : B.IsScFredholmSectionTame f), B.IsProper f →
        SectionOrientation f hf.toIsScFredholmSection →
          ∀ k : ℕ, (BundledMPolyfold.of PX).scDeRham k →ₗ[ℝ] ℝ,
      (∀ (f : X → Y) (hf : B.IsScFredholmSectionTame f) (hP : B.IsProper f)
          (o : SectionOrientation f hf.toIsScFredholmSection) (N : B.One → ℝ), B.IsAuxNorm N →
        (∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
          ∀ C : ℝ, 0 < C → IsCompact (closure {x ∈ U | B.AuxLe N (f x) C})) ∧
        ∀ U : Set X, IsOpen U → solutionSet P f ⊆ U →
          (∀ C : ℝ, 0 < C → IsCompact (closure {x ∈ U | B.AuxLe N (f x) C})) →
          (∃ s, B.IsAdmissible f N U s) ∧
          ∀ (s : X → Y) (hs : B.IsAdmissible f N U s) (n : ℕ),
            (∀ x ∈ PX.smoothSet, B.IsIndexAt f x n) →
            IsCompact (solutionSet P (sectionAdd P f s)) ∧
            B.solPart f s n = solutionSet P (sectionAdd P f s) ∧
            (∀ c : LinearMap.ker ((BundledMPolyfold.of PX).formsInftyD n),
              letI := solPartChartedSpace hX hf hs n
              haveI := isManifold_solPart hX hf hs n
              Φ f hf hP o n ((BundledMPolyfold.of PX).scDeRhamMk n c) =
                ManifoldForm.integral (solPartOr hX hf hs o n)
                  (formsInftyRestrict n (hasCornerStructureOfDim_solPart hX hf hs n)
                    (c : (BundledMPolyfold.of PX).formsInfty n))) ∧
            ∀ k : ℕ, k ≠ n → Φ f hf hP o k = 0) ∧
      ∀ (f₀ : X → Y) (hf₀ : B.IsScFredholmSectionTame f₀) (hP₀ : B.IsProper f₀)
        (o₀ : SectionOrientation f₀ hf₀.toIsScFredholmSection)
        (S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))
        (hf₁ : B.IsScFredholmSectionTame (sectionAdd P f₀ (pullbackSlice S 1)))
        (hP₁ : B.IsProper (sectionAdd P f₀ (pullbackSlice S 1)))
        (o₁ : SectionOrientation (sectionAdd P f₀ (pullbackSlice S 1)) hf₁.toIsScFredholmSection),
        IsProperOrientedHomotopyBetween hf₀ o₀ S o₁ →
          ∀ k : ℕ, Φ f₀ hf₀ hP₀ o₀ k = Φ _ hf₁ hP₁ o₁ k :=
  theorem_6_7_1_noBoundary_of_indep hX hbump hbd
    (psiAt_eq_of_admissible_of_orientation hX hbump hOr)
    (psiAt_eq_of_homotopy_of_orientation hX hbump hOr)

end Theorem

end Polyfold
