import Polyfold.Chapter9.FaceChange

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, §9.5, Theorems 9.5.15–9.5.18 (pp. 448–451; gaps G.109, G.110), and Part I, Theorem
4.4.7 (p. 199).  Numbers and pages are the 2021 text's.

# Part I's face integrand is the density on the boundary stratum

Part I's boundary integral (`ManifoldForm.boundaryIntegral`) sums, over signed corner charts `e`
of the manifold with corners `M` and the faces `{yₗ = 0}`, the integrals of
`faceSign l · ιₗ^*(e⁻¹)^*ω` over `ιₗ⁻¹(e(U))`.

## What is formalized

* **`FormEval.orSign_mul_faceSign_mul_facePullback_eq`**: at a point `u` of the open face
  piece where the tangent orientation `bridgeOrientation o` reads in `κ` as `signedOr b` of the
  standard one, `orSign b · faceSign l · ιₗ^*(κ⁻¹)^*η (u)(e₁, …, e_m)` is the face density
  `± ω(Tι(ιₗ e₁), …, Tι(ιₗ e_m))` for the boundary orientation `o_{∂M}` (Definition 9.3.8), when
  `η` is the restriction of `ω` to `M`.
* `ManifoldForm.integrableOn_facePullback_chartForm`: the face integrands of a form continuous
  in a chart and vanishing off a compact subset of its source are integrable.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module Manifold

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

universe u

namespace ManifoldForm

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant (m + 1)) M]

/-- **The face integrands are integrable**: for a form `ω` continuous in the chart `e` and
vanishing outside a compact subset of its source, `u ↦ ιₗ^*(e⁻¹)^*ω (u)(e₁, …, e_m)` is
integrable on `ιₗ⁻¹(e(U))`. -/
theorem integrableOn_facePullback_chartForm
    {e : OpenPartialHomeomorph M (EuclideanQuadrant (m + 1))}
    {ω : ManifoldForm (𝓠 (m + 1)) M m}
    (hω : ContinuousOn (chartForm (𝓠 (m + 1)) e ω) (e.extend (𝓠 (m + 1))).target) {K : Set M}
    (hK : IsCompact K) (hKe : K ⊆ e.source) (hω0 : ∀ x ∉ K, ω x = 0) (l : Fin (m + 1)) :
    IntegrableOn (fun u => facePullback l (chartForm (𝓠 (m + 1)) e ω) u (stdFrame m))
      (faceEmbedding l ⁻¹' (e.extend (𝓠 (m + 1))).target) := by
  set T := (e.extend (𝓠 (m + 1))).target
  have hCK : IsCompact (e.extend (𝓠 (m + 1)) '' K) :=
    hK.image_of_continuousOn (e.continuousOn_extend.mono (by rwa [e.extend_source]))
  have hCt : e.extend (𝓠 (m + 1)) '' K ⊆ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact (e.extend (𝓠 (m + 1))).map_source (by rw [e.extend_source]; exact hKe hx)
  have hemb : Topology.IsClosedEmbedding (faceEmbedding l) :=
    LinearMap.isClosedEmbedding_of_injective (f := (faceEmbedding l :
      EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1))))
      (LinearMap.ker_eq_bot.2 (MPolyfold.faceEmbedding_injective l))
  have hCK' : IsCompact (faceEmbedding l ⁻¹' (e.extend (𝓠 (m + 1)) '' K)) :=
    hemb.isCompact_preimage hCK
  have hc : ContinuousOn (fun u => facePullback l (chartForm (𝓠 (m + 1)) e ω) u (stdFrame m))
      (faceEmbedding l ⁻¹' T) := by
    have h1 : ContinuousOn (fun u => chartForm (𝓠 (m + 1)) e ω (faceEmbedding l u))
        (faceEmbedding l ⁻¹' T) :=
      hω.comp (faceEmbedding l).continuous.continuousOn fun _ hu => hu
    exact (ContinuousAlternatingMap.apply ℝ _ ℝ
      (faceEmbedding l ∘ stdFrame m)).continuous.comp_continuousOn h1
  have hTm : MeasurableSet (faceEmbedding l ⁻¹' T) :=
    (faceEmbedding l).continuous.measurable (measurableSet_extend_target e)
  refine IntegrableOn.of_forall_sdiff_eq_zero
    ((hc.mono fun u hu => hCt hu).integrableOn_compact hCK') hTm fun u hu => ?_
  have : (e.extend (𝓠 (m + 1))).symm (faceEmbedding l u) ∉ K := fun h => hu.2
    ⟨_, h, (e.extend (𝓠 (m + 1))).right_inv hu.1⟩
  change chartForm (𝓠 (m + 1)) e ω (faceEmbedding l u) (faceEmbedding l ∘ stdFrame m) = 0
  rw [chartForm_eq_zero_of_notMem hω0 e this]
  rfl

end ManifoldForm

namespace EpGroupoid

open MPolyfold

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {m : ℕ} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω] {M : Set Obj} [ParacompactSpace M]
  {hY : X.PObj.IsSubMPolyfold M} {hcs : (subPolyfold hY).HasCornerStructureOfDim (m + 1)}
  [inst : ChartedSpace (EuclideanQuadrant (m + 1)) M]
  (hch : inst = (subPolyfold hY).cornerChartedSpace hcs)
include hch

open Classical in
/-- **Part I's face integrand is the density on the boundary stratum**: for a Mathlib `m`-form
`η` on `M` which is the restriction of `ω` (its values are those of `ω` on the frames `Tι(v)`),
corner coordinates `κ` of `M`, a point `u` of the open face piece of `{yₗ = 0}` at which the
tangent orientation `bridgeOrientation o` reads in `κ` as `signedOr b` of the standard one,
`orSign b · faceSign l · ιₗ^*(κ⁻¹)^*η (u)(e₁, …, e_m) = ± ω(Tι(ιₗ e₁), …, Tι(ιₗ e_m))`, the sign
`+` iff the face frame is positive for the boundary orientation `o_{∂M}`. -/
theorem FormEval.orSign_mul_faceSign_mul_facePullback_eq (F : X.FormEval m Ω)
    (hM : X.PObj.IsSubmanifoldOfDim M (m + 1)) (ht : X.PObj.HasTameInducedStructure M)
    (o : X.PObj.SubmanifoldOrientation M (m + 1)) (ω : Ω)
    (η : ManifoldForm (𝓠 (m + 1)) M m)
    (hη : ∀ (y : M) (v : Fin m → EuclideanSpace ℝ (Fin (m + 1))),
      η y v = F.ev ω fun i => incFrame hcs (hcs.coords y) (hcs.mem_coords y) (v i))
    (κ : CornerCoords (subPolyfold hY) (m + 1)) (l : Fin (m + 1))
    {u : EuclideanSpace ℝ (Fin m)} (hu : u ∈ κ.faceSet l) (b : Bool)
    (hb : orientationIn κ.toQuadrantChart (κ.facePt l u)
      (bridgeOrientation hcs o (κ.facePt l u)) = signedOr b (stdOrientation (m + 1))) :
    orSign b * faceSign l *
        facePullback l (ManifoldForm.chartForm (𝓠 (m + 1)) κ.toQuadrantChart η) u (stdFrame m) =
      F.faceDensity hcs (o.stratumOrientation hM ht).frames ω κ l (κ.facePt l u) := by
  have hb' := hb
  rw [orientationIn_bridgeOrientation hch (Nat.succ_pos m) hM o κ
    (CornerCoords.facePt_mem_s hu)] at hb'
  subst hch
  let _ : ChartedSpace (EuclideanQuadrant (m + 1)) M := (subPolyfold hY).cornerChartedSpace hcs
  set y := κ.facePt l u with hydef
  have hy : y ∈ κ.s := CornerCoords.facePt_mem_s hu
  have hpiece : y ∈ κ.facePiece l := CornerCoords.facePt_mem_facePiece hu
  have hyl : κ.coord y l = 0 := CornerCoords.coord_facePt_self hu
  have hyy : y ∈ (hcs.coords y).s := hcs.mem_coords y
  have hval : facePullback l (ManifoldForm.chartForm (𝓠 (m + 1)) κ.toQuadrantChart η) u
      (stdFrame m) = F.ev ω (faceFrame hcs κ hy l) := by
    rw [facePullback, formPullback_apply, ManifoldForm.chartForm_apply]
    refine (hη y _).trans ?_
    congr 1
    funext k
    have h1 := fiberMap_chartChange (hcs := hcs) rfl κ (hcs.coords y) hy hyy
      (faceEmbedding l (stdFrame m k))
    change MPolyfold.tangentMap (subPolyfold_inclusion_isScSmooth hY)
      ((hcs.coords y).fiberMap (x := hcs.levelOne y) _
        (chartChangeDeriv (𝓠 (m + 1)) κ.toQuadrantChart (hcs.coords y).toQuadrantChart y
          (faceEmbedding l (stdFrame m k)))).1 =
      MPolyfold.tangentMap (subPolyfold_inclusion_isScSmooth hY)
        (κ.fiberMap (x := hcs.levelOne y) _ (faceEmbedding l (stdFrame m k))).1
    rw [h1]
  rw [hval, FormEval.faceDensity, dif_pos hy, orSign_mul_faceSign]
  have hiff := faceFrame_mem_stratumOrientation_iff hM ht o κ hpiece hyl b hb'
  by_cases h : (b == faceBool l) = true
  · rw [if_pos h, if_pos (hiff.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.1 h'))]

end EpGroupoid

end Polyfold
