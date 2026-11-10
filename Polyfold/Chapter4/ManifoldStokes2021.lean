import Polyfold.Chapter4.ManifoldIntegral2021
import Polyfold.Chapter4.EuclideanStokes2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021): **Stokes' theorem on a
compact oriented manifold with boundary with corners**, the classical theorem under
**Theorem 4.4.7** (p. 199; preprint Theorem 4.28, gap G.40) and **Theorem 6.7.1** (p. 277), with
boundary orientation of **Definition 9.3.8** (p. 427, outward vector first; Definition 9.3.10,
p. 428, names it the induced orientation).  Numbers and pages are the 2021 text's.

# Stokes' theorem on a Mathlib manifold with corners

`M` is a `C^∞` manifold modelled on `modelWithCornersEuclideanQuadrant (n + 1)` (the quadrant
`[0,∞)ⁿ⁺¹`), with a continuous tangent orientation `o`; `ω` is a `C¹` `n`-form.

## The boundary integral

In a chart `e` the boundary of `M` is the union of the faces `{xᵢ = 0}` of the chart target
`e(U) = U' ∩ [0,∞)ⁿ⁺¹`; the face `{xᵢ = 0}` is parametrized by `faceEmbedding i`, and its
boundary orientation (outward vector `-eᵢ` first, Definition 9.3.8) is `faceSign i` times the one
of the parametrization (`det_cons_neg_stdFrame_faceFrame`, `EuclideanForms2021.lean`).  So the
boundary integral of `ω` in a chart signed by `b` is
`orSign b · ∑ᵢ faceSign i · ∫_{ιᵢ⁻¹(e(U))} ιᵢ^*(e⁻¹)^*ω` (`chartBoundaryIntegral`), and with
integration data `D` (`ManifoldIntegral2021.lean`)
`∫_{∂M} ω = ∑ⱼ (±ⱼ) ∑ᵢ faceSign i ∫ ιᵢ^*(e_j⁻¹)^*(ρⱼ ω)` (`IntegrationData.boundaryIntegral`).
The corners (points on two faces) form a null set of every face (`openQuadrant_ae_eq_quadrant`),
so `∑ᵢ` is the integral over the boundary points of degeneracy index `1`, where
Definition 9.3.8 orients `∂M`.

## What is formalized

* `chartIntegral_extDeriv_eq`: Stokes in one chart, for a `C¹` form vanishing outside a compact
  subset of the chart source (`stokes_quadrant_inter_open` and the chart independence of `d`,
  `chartForm_extDeriv_of_mem_target`).
* **`IntegrationData.stokes`**: `∫_M dω = ∫_{∂M} ω` for integration data `D` on `s` and a `C¹`
  form with compact support in `s`: `dω = ∑ⱼ d(ρⱼ ω)`, each `d(ρⱼ ω)` lives in one signed chart.
* `IntegrationData.boundaryIntegral_eq`: the boundary integral of a `C¹` form does not depend on
  the integration data (a consequence of Stokes' theorem and the independence of `∫_M`).
* **`ManifoldForm.integral_extDeriv_eq_boundaryIntegral`**: `∫_M dω = ∫_{∂M} ω` for the integrals
  `ManifoldForm.integral` and `ManifoldForm.boundaryIntegral`, on a Hausdorff σ-compact `M` (for
  instance compact) and a `C¹` form with compact support; `stokes_of_compactSpace` for compact
  `M`.  Reversing the orientation changes the sign of `∫_{∂M}` (`boundaryIntegral_neg_orientation`).
* The linear algebra of the induced orientation across charts: `faceProjection`, `faceRestrict`
  (`Ā = π_j ∘ A ∘ ιᵢ`), `faceSign_mul_det_eq` (`faceSign i · det A = (A eᵢ)_j · faceSign j · det Ā`
  for `A` mapping `{xᵢ = 0}` into `{x_j = 0}`) and `orSign_faceSign_mul_det_faceRestrict_pos`;
  `ManifoldBoundary2021.lean` applies them to the chart changes.
-/

open Set Filter Topology Manifold Module MeasureTheory

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- Mathlib's model with corners `[0,∞)ⁿ ⊆ ℝⁿ`. -/
local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

/-! ### The induced orientation of the faces across charts (linear algebra) -/

section FaceOrientation

variable {n : ℕ}

/-- The projection `x ↦ (x_k)_{k ≠ j}`, `ℝⁿ⁺¹ → ℝⁿ`, a left inverse of `faceEmbedding j` on the
hyperplane `{x_j = 0}`. -/
def faceProjection (j : Fin (n + 1)) :
    EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (j.removeNth (WithLp.ofLp x))
      map_add' := fun x y => by ext k; simp [Fin.removeNth]
      map_smul' := fun c x => by ext k; simp [Fin.removeNth] }

theorem faceProjection_apply (j : Fin (n + 1)) (x : EuclideanSpace ℝ (Fin (n + 1))) (k : Fin n) :
    faceProjection j x k = x (j.succAbove k) := rfl

/-- **The restriction of a linear map to the faces**: `Ā = π_j ∘ A ∘ ιᵢ : ℝⁿ → ℝⁿ`, the
derivative of the face transition `{xᵢ = 0} → {x_j = 0}` when `A` is the derivative of a chart
change mapping the face `{xᵢ = 0}` to the face `{x_j = 0}`. -/
def faceRestrict (A : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (i j : Fin (n + 1)) : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (faceProjection j).comp (A.comp (faceEmbedding i))

theorem apply_faceEmbedding_eq
    {A : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))}
    {i j : Fin (n + 1)} (hA : ∀ y, A (faceEmbedding i y) j = 0) (y : EuclideanSpace ℝ (Fin n)) :
    A (faceEmbedding i y) = faceEmbedding j (faceRestrict A i j y) :=
  (faceEmbedding_removeNth (hA y)).symm

theorem faceSign_mul_self (i : Fin (n + 1)) : faceSign i * faceSign i = 1 := by
  rw [faceSign, ← pow_add, ← two_mul, pow_mul]; norm_num

/-- A top-degree alternating map on `ℝⁿ` scales by the determinant (the algebraic form of
`alternatingMap_comp_eq_det_mul`). -/
theorem alternatingMap_comp_stdFrame (g : EuclideanSpace ℝ (Fin n) [⋀^Fin n]→ₗ[ℝ] ℝ)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    g (B ∘ stdFrame n) = B.det * g (stdFrame n) := by
  set b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have key : ∀ w, g w = g b * b.det w := fun w => by
    simpa using congrArg (fun h => h w) (AlternatingMap.eq_smul_basis_det b g)
  have hc := b.det_comp B.toLinearMap b
  simp only [ContinuousLinearMap.coe_coe] at hc
  rw [key, key (stdFrame n), ← coe_basisFun_toBasis, hc, b.det_self, ContinuousLinearMap.det]
  ring

/-- `n + 1` vectors in the image of a face embedding have determinant `0`. -/
theorem det_faceEmbedding_comp_eq_zero (j : Fin (n + 1))
    (v : Fin (n + 1) → EuclideanSpace ℝ (Fin n)) :
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.det (faceEmbedding j ∘ v) = 0 := by
  have hni : ¬ LinearIndependent ℝ (faceEmbedding j ∘ v) := fun h => by
    have hv : LinearIndependent ℝ v := by
      have h2 : LinearIndependent ℝ ((faceEmbedding j).toLinearMap ∘ v) := by
        rw [ContinuousLinearMap.coe_coe]; exact h
      exact h2.of_comp
    have h' := hv.fintype_card_le_finrank
    rw [Fintype.card_fin, finrank_euclideanSpace_fin] at h'
    omega
  exact AlternatingMap.map_linearDependent _ _ hni

/-- **The induced orientation of the faces, the linear algebra**: for a linear map `A` of `ℝⁿ⁺¹`
mapping the hyperplane `{xᵢ = 0}` into `{x_j = 0}`,
`faceSign i · det A = (A eᵢ)_j · faceSign j · det Ā`, `Ā = faceRestrict A i j`.  With
`det_cons_neg_stdFrame_faceFrame` this says: `(−eᵢ, (e_k)_{k≠i})` and its image under `A` are
compared through the outward components, the outward vector being first (Definition 9.3.8). -/
theorem faceSign_mul_det_eq
    {A : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))}
    {i j : Fin (n + 1)} (hA : ∀ y, A (faceEmbedding i y) j = 0) :
    faceSign i * A.det = A (stdFrame (n + 1) i) j * (faceSign j * (faceRestrict A i j).det) := by
  set b := (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis
  set e := stdFrame (n + 1)
  set c := A (e i) j
  set u := faceProjection j (A (e i))
  set W := faceEmbedding j ∘ (faceRestrict A i j ∘ stdFrame n)
  -- the decomposition `A eᵢ = c e_j + ι_j u`
  have hdec : A (e i) = c • e j + faceEmbedding j u := by
    ext k
    rcases Fin.eq_self_or_eq_succAbove j k with rfl | ⟨l, rfl⟩
    · simp [e, c, stdFrame_apply]
    · simp [e, c, u, stdFrame_apply, faceProjection_apply, (Fin.succAbove_ne j l)]
  have hW : A ∘ (faceEmbedding i ∘ stdFrame n) = W := by
    funext l; exact apply_faceEmbedding_eq hA _
  have h1 : faceSign i * A.det = b.det (Fin.cons (-A (e i)) W) := by
    rw [← det_cons_neg_stdFrame_faceFrame i, mul_comm, ContinuousLinearMap.det,
      ← b.det_comp A.toLinearMap, Fin.comp_cons]
    simp only [ContinuousLinearMap.coe_coe, map_neg]
    rw [hW]
  have h2 : b.det (Fin.cons (-A (e i)) W) =
      c * b.det (Fin.cons (-e j) W) + b.det (Fin.cons (faceEmbedding j (-u)) W) := by
    rw [hdec, neg_add, ← smul_neg, map_neg]
    have hadd := b.det.toMultilinearMap.cons_add W (c • -e j) (-faceEmbedding j u)
    have hsmul := b.det.toMultilinearMap.cons_smul W c (-e j)
    simp only [AlternatingMap.coe_multilinearMap] at hadd hsmul
    rw [hadd, hsmul, smul_eq_mul]
  have h3 : b.det (Fin.cons (faceEmbedding j (-u)) W) = 0 := by
    rw [show W = faceEmbedding j ∘ (faceRestrict A i j ∘ stdFrame n) from rfl, ← Fin.comp_cons]
    exact det_faceEmbedding_comp_eq_zero j _
  have h4 : b.det (Fin.cons (-e j) W) = (faceRestrict A i j).det * faceSign j := by
    set g := (b.det.curryLeft (-e j)).compLinearMap (faceEmbedding j).toLinearMap
    have hg : ∀ v, g v = b.det (Fin.cons (-e j) (faceEmbedding j ∘ v)) := fun v => rfl
    rw [← det_cons_neg_stdFrame_faceFrame j, ← hg, ← hg]
    exact alternatingMap_comp_stdFrame g _
  rw [h1, h2, h3, h4]
  ring

/-- **The induced orientation agrees across charts** (the linear-algebra step of the
independence of the boundary orientation, Definition 9.3.8): let `A` be the derivative of a chart
change at a boundary point of degeneracy index `1`, mapping the face `{xᵢ = 0}` of the first chart
into the face `{x_j = 0}` of the second and the inward vector `eᵢ` to an inward vector
(`(A eᵢ)_j > 0`), the charts being signed by `b`, `b'` (`orSign b · orSign b' · det A > 0`).  In
the face parametrizations, the boundary orientation reads as `orSign b · faceSign i` and as
`orSign b' · faceSign j` (outward vector first); the face transition, with derivative
`Ā = faceRestrict A i j`, has `sign det Ā` equal to their product: the two readings agree. -/
theorem orSign_faceSign_mul_det_faceRestrict_pos
    {A : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))}
    {i j : Fin (n + 1)} (hA : ∀ y, A (faceEmbedding i y) j = 0)
    (hin : 0 < A (stdFrame (n + 1) i) j) {b b' : Bool}
    (hdet : 0 < orSign b * orSign b' * A.det) :
    0 < orSign b * faceSign i * (orSign b' * faceSign j) * (faceRestrict A i j).det := by
  have key := faceSign_mul_det_eq hA
  have hsq := faceSign_mul_self i
  have : A (stdFrame (n + 1) i) j *
      (orSign b * faceSign i * (orSign b' * faceSign j) * (faceRestrict A i j).det) =
      orSign b * orSign b' * A.det := by
    calc A (stdFrame (n + 1) i) j *
          (orSign b * faceSign i * (orSign b' * faceSign j) * (faceRestrict A i j).det)
        = orSign b * orSign b' * faceSign i *
            (A (stdFrame (n + 1) i) j * (faceSign j * (faceRestrict A i j).det)) := by ring
      _ = orSign b * orSign b' * A.det * (faceSign i * faceSign i) := by rw [← key]; ring
      _ = _ := by rw [hsq, mul_one]
  exact pos_of_mul_pos_right (this ▸ hdet) hin.le

end FaceOrientation

namespace ManifoldForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant (n + 1)) M]

/-- **The boundary integral of an `n`-form in a chart** `e` of an `(n+1)`-manifold with corners:
`∑ᵢ faceSign i · ∫_{ιᵢ⁻¹(e(U))} ιᵢ^*(e⁻¹)^*ω`, the sum over the faces `{xᵢ = 0}` of the chart
target, each with the boundary orientation (outward vector first, Definition 9.3.8) relative to
the standard orientation of `ℝⁿ⁺¹`. -/
def chartBoundaryIntegral (e : OpenPartialHomeomorph M (EuclideanQuadrant (n + 1)))
    (ω : ManifoldForm (𝓠 (n + 1)) M n) : ℝ :=
  ∑ i : Fin (n + 1), faceSign i *
    topFormIntegral (faceEmbedding i ⁻¹' (e.extend (𝓠 (n + 1))).target)
      (facePullback i (chartForm (𝓠 (n + 1)) e ω))

omit [ChartedSpace (EuclideanQuadrant (n + 1)) M] in
/-- The chart target is `U ∩ closedQuadrant univ` with `U` open. -/
theorem extend_target_eq_inter_quadrant (e : OpenPartialHomeomorph M (EuclideanQuadrant (n + 1))) :
    (e.extend (𝓠 (n + 1))).target =
      (𝓠 (n + 1)).symm ⁻¹' e.target ∩
        closedQuadrant ((Finset.univ : Finset (Fin (n + 1))) : Set _) := by
  rw [e.extend_target, range_modelWithCornersEuclideanQuadrant, Finset.coe_univ]

variable [IsManifold (𝓠 (n + 1)) ∞ M]

/-- **Stokes' theorem in one chart**: for a `C¹` `n`-form `η` vanishing outside a compact subset
`K` of the source of the chart at `x₀`, `∫_{x₀} dη = ∑ᵢ faceSign i ∫ ιᵢ^*(e⁻¹)^*η`
(`stokes_quadrant_inter_open` on the chart target, with `chartForm_extDeriv_of_mem_target`). -/
theorem chartIntegral_extDeriv_eq {η : ManifoldForm (𝓠 (n + 1)) M n}
    (hη : ContMDiffForm (𝓠 (n + 1)) 1 η) {x₀ : M} {K : Set M} (hK : IsCompact K)
    (hKe : K ⊆ (chartAt (EuclideanQuadrant (n + 1)) x₀).source) (hη0 : ∀ x ∉ K, η x = 0) :
    chartIntegral (chartAt (EuclideanQuadrant (n + 1)) x₀) (extDeriv η) =
      chartBoundaryIntegral (chartAt (EuclideanQuadrant (n + 1)) x₀) η := by
  set e := chartAt (EuclideanQuadrant (n + 1)) x₀ with he_def
  have he : e ∈ IsManifold.maximalAtlas (𝓠 (n + 1)) ∞ M :=
    IsManifold.chart_mem_maximalAtlas x₀
  set T := (e.extend (𝓠 (n + 1))).target with hT_def
  set U := (𝓠 (n + 1)).symm ⁻¹' e.target with hU_def
  have hU : IsOpen U := e.open_target.preimage (𝓠 (n + 1)).continuous_symm
  have hT : T = U ∩ closedQuadrant ((Finset.univ : Finset (Fin (n + 1))) : Set _) :=
    extend_target_eq_inter_quadrant e
  -- the support in the chart
  set K' := e.extend (𝓠 (n + 1)) '' K
  have hK' : IsCompact K' :=
    hK.image_of_continuousOn (e.continuousOn_extend.mono (by rwa [e.extend_source]))
  have hK'T : K' ⊆ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact (e.extend (𝓠 (n + 1))).map_source (by rw [e.extend_source]; exact hKe hx)
  have hK'U : K' ⊆ U := fun y hy => by
    have := hK'T hy
    rw [hT] at this
    exact this.1
  have h0 : ∀ y ∈ U ∩ closedQuadrant ((Finset.univ : Finset (Fin (n + 1))) : Set _), y ∉ K' →
      chartForm (𝓠 (n + 1)) e η y = 0 := by
    intro y hy hyK
    rw [← hT] at hy
    refine chartForm_eq_zero_of_notMem hη0 e fun hK => hyK ⟨_, hK, ?_⟩
    exact (e.extend (𝓠 (n + 1))).right_inv hy
  have hC : ContDiffOn ℝ 1 (chartForm (𝓠 (n + 1)) e η)
      (U ∩ closedQuadrant ((Finset.univ : Finset (Fin (n + 1))) : Set _)) := by
    rw [← hT]; exact hη x₀
  have key := stokes_quadrant_inter_open Finset.univ hU hK' hK'U h0 hC
  rw [← hT] at key
  rw [chartIntegral, topFormIntegral_congr (measurableSet_extend_target e)
    fun y hy => chartForm_extDeriv_of_mem_target he hη hy, key, chartBoundaryIntegral]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hT_def, hT, preimage_inter, preimage_faceEmbedding_quadrant]

end ManifoldForm

namespace IntegrationData

open ManifoldForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant (n + 1)) M]
  [IsManifold (𝓠 (n + 1)) ∞ M] {o : TangentOrientation (𝓠 (n + 1)) M (n + 1)} {s : Set M}
  {ι : Type*} [Fintype ι] (D : IntegrationData M o s ι)

/-- **The boundary integral `∫_{∂M} ω` with respect to integration data** `D`:
`∑ⱼ (±ⱼ) ∑ᵢ faceSign i ∫ ιᵢ^*(e_j⁻¹)^*(ρⱼ ω)`, the faces of the charts with the boundary
orientation of Definition 9.3.8 (outward vector first). -/
def boundaryIntegral (ω : ManifoldForm (𝓠 (n + 1)) M n) : ℝ :=
  ∑ j, orSign (D.sign j) * chartBoundaryIntegral (D.chart j) (smulFun (D.ρ j) ω)

omit [IsManifold (𝓠 (n + 1)) ∞ M] in
/-- Reversing the orientation changes the sign of the boundary integral. -/
theorem boundaryIntegral_neg (ω : ManifoldForm (𝓠 (n + 1)) M n) :
    D.neg.boundaryIntegral ω = -D.boundaryIntegral ω := by
  simp only [boundaryIntegral, neg, orSign_not, neg_mul, Finset.sum_neg_distrib]

/-- **Stokes' theorem with respect to integration data** (the global step towards Theorem 4.4.7,
2021 p. 199, and Theorem 6.7.1): for a `C¹` `n`-form `ω` with compact support in `s`,
`∫_M dω = ∫_{∂M} ω`, both integrals taken with respect to `D`, `∂M` with the induced orientation
(outward vector first, Definition 9.3.8). -/
theorem stokes {ω : ManifoldForm (𝓠 (n + 1)) M n} (hω : ContMDiffForm (𝓠 (n + 1)) 1 ω)
    (hc : IsCompact (tsupport ω)) (hs : tsupport ω ⊆ s) :
    D.integral (extDeriv ω) = D.boundaryIntegral ω := by
  have hω0 : ∀ x ∉ tsupport ω, ω x = 0 := fun x hx => eq_zero_of_notMem_tsupport hx
  have hC1 : ∀ j, ContMDiffForm (𝓠 (n + 1)) 1 (smulFun (D.ρ j) ω) := fun j =>
    D.contMDiffForm_smulFun (r := 1) (by norm_cast) j hω
  have hKj : ∀ j, IsCompact (_root_.tsupport (D.ρ j) ∩ tsupport ω) := fun j =>
    hc.inter_left (isClosed_tsupport _)
  have hdj0 : ∀ j, ∀ x ∉ _root_.tsupport (D.ρ j) ∩ tsupport ω,
      extDeriv (smulFun (D.ρ j) ω) x = 0 := fun j x hx =>
    extDeriv_eq_zero_of_notMem_tsupport fun h => hx (tsupport_smulFun_subset _ _ h)
  -- `dω = ∑ⱼ d(ρⱼ ω)`
  have hsum : extDeriv ω = ∑ j, extDeriv (smulFun (D.ρ j) ω) := by
    conv_lhs => rw [← finsetSum_smulFun_eq_self Finset.univ D.sum_eq_one hs hω0]
    exact extDeriv_finsetSum Finset.univ fun j _ => hC1 j
  rw [hsum, D.integral_finsetSum Finset.univ (fun j _ => contMDiffForm_zero_extDeriv (hC1 j))
    (fun j _ => hKj j) (fun j _ => hdj0 j), boundaryIntegral]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [D.integral_eq_chartIntegral (contMDiffForm_zero_extDeriv (hC1 j)) (D.region_subset j)
    (D.orientationIn_eq j) (hKj j) (fun x hx => D.tsupport_subset j hx.1)
    (fun x hx => hs hx.2) (hdj0 j),
    chartIntegral_extDeriv_eq (hC1 j) (hKj j)
      (fun x hx => D.region_subset j (D.tsupport_subset j hx.1))
      fun x hx => smulFun_eq_zero_of_notMem hω0 hx]

/-- **The boundary integral does not depend on the integration data**, for a `C¹` form with
compact support in both domains (both are `∫_M dω`, which does not depend on them). -/
theorem boundaryIntegral_eq {s' : Set M} {ι' : Type*} [Fintype ι']
    (D' : IntegrationData M o s' ι') {ω : ManifoldForm (𝓠 (n + 1)) M n}
    (hω : ContMDiffForm (𝓠 (n + 1)) 1 ω) (hc : IsCompact (tsupport ω)) (hs : tsupport ω ⊆ s)
    (hs' : tsupport ω ⊆ s') : D.boundaryIntegral ω = D'.boundaryIntegral ω := by
  rw [← D.stokes hω hc hs, ← D'.stokes hω hc hs']
  exact D.integral_eq D' (contMDiffForm_zero_extDeriv hω) hc hs hs'
    fun x hx => extDeriv_eq_zero_of_notMem_tsupport hx

end IntegrationData

namespace ManifoldForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant (n + 1)) M]
  [IsManifold (𝓠 (n + 1)) ∞ M]

open Classical in
/-- **The boundary integral `∫_{∂M} ω` of an `n`-form** over the boundary of the
`(n+1)`-manifold with corners `M`, with the orientation induced by `o` (outward vector first,
Definition 9.3.8): the boundary integral with respect to a chosen integration datum on the support
of `ω` (`0` if there is none).  For a `C¹` compactly supported form it does not depend on the
choice (`IntegrationData.boundaryIntegral_eq`, `boundaryIntegral_eq_integrationData`). -/
def boundaryIntegral (o : TangentOrientation (𝓠 (n + 1)) M (n + 1))
    (ω : ManifoldForm (𝓠 (n + 1)) M n) : ℝ :=
  if h : ∃ T : Finset M, Nonempty (IntegrationData M o (tsupport ω) {x // x ∈ T}) then
    (Classical.choice h.choose_spec).boundaryIntegral ω
  else 0

variable [T2Space M] [SigmaCompactSpace M] {o : TangentOrientation (𝓠 (n + 1)) M (n + 1)}

/-- `∫_{∂M} ω` is the boundary integral with respect to any integration datum whose domain
contains the support of the `C¹` compactly supported form `ω`. -/
theorem boundaryIntegral_eq_integrationData (ho : o.IsContinuous (𝓠 (n + 1)) ∞)
    {ω : ManifoldForm (𝓠 (n + 1)) M n} (hω : ContMDiffForm (𝓠 (n + 1)) 1 ω)
    (hc : IsCompact (tsupport ω)) {s : Set M} {ι : Type*} [Fintype ι]
    (D : IntegrationData M o s ι) (hs : tsupport ω ⊆ s) :
    boundaryIntegral o ω = D.boundaryIntegral ω := by
  have h := exists_integrationData ho hc
  rw [boundaryIntegral, dif_pos h]
  exact (Classical.choice h.choose_spec).boundaryIntegral_eq D hω hc subset_rfl hs

/-- **Reversing the orientation changes the sign of `∫_{∂M} ω`.** -/
theorem boundaryIntegral_neg_orientation (ho : o.IsContinuous (𝓠 (n + 1)) ∞)
    {ω : ManifoldForm (𝓠 (n + 1)) M n} (hω : ContMDiffForm (𝓠 (n + 1)) 1 ω)
    (hc : IsCompact (tsupport ω)) : boundaryIntegral (-o) ω = -boundaryIntegral o ω := by
  obtain ⟨T, ⟨D⟩⟩ := exists_integrationData ho hc
  rw [boundaryIntegral_eq_integrationData ho.neg hω hc D.neg subset_rfl,
    boundaryIntegral_eq_integrationData ho hω hc D subset_rfl, D.boundaryIntegral_neg]

/-- **Stokes' theorem on an oriented manifold with boundary with corners** (the classical theorem
under Theorem 4.4.7, 2021 p. 199, preprint Theorem 4.28, and Theorem 6.7.1): for a Hausdorff
σ-compact `C^∞` manifold `M` modelled on `[0,∞)ⁿ⁺¹` with a continuous tangent orientation `o` and
a `C¹` `n`-form `ω` with compact support, `∫_M dω = ∫_{∂M} ω`, the boundary with the induced
orientation (outward vector first, Definition 9.3.8).  The text's Theorem 4.4.7 is the case of the
restriction of an sc-differential form to a compact finite-dimensional submanifold `N` of an
M-polyfold (gap G.80). -/
theorem integral_extDeriv_eq_boundaryIntegral (ho : o.IsContinuous (𝓠 (n + 1)) ∞)
    {ω : ManifoldForm (𝓠 (n + 1)) M n} (hω : ContMDiffForm (𝓠 (n + 1)) 1 ω)
    (hc : IsCompact (tsupport ω)) :
    integral o (extDeriv ω) = boundaryIntegral o ω := by
  obtain ⟨T, ⟨D⟩⟩ := exists_integrationData ho hc
  rw [integral_eq_integrationData ho (contMDiffForm_zero_extDeriv hω)
    (hc.of_isClosed_subset isClosed_closure (tsupport_extDeriv_subset ω)) D
    (tsupport_extDeriv_subset ω), boundaryIntegral_eq_integrationData ho hω hc D subset_rfl]
  exact D.stokes hω hc subset_rfl

/-- **Stokes' theorem on a compact oriented manifold with boundary with corners**: for `M`
compact, Hausdorff, modelled on `[0,∞)ⁿ⁺¹`, a continuous tangent orientation `o` and a `C¹`
`n`-form `ω`, `∫_M dω = ∫_{∂M} ω` (Theorem 4.4.7, 2021 p. 199, for classical forms). -/
theorem stokes_of_compactSpace [CompactSpace M] (ho : o.IsContinuous (𝓠 (n + 1)) ∞)
    {ω : ManifoldForm (𝓠 (n + 1)) M n} (hω : ContMDiffForm (𝓠 (n + 1)) 1 ω) :
    integral o (extDeriv ω) = boundaryIntegral o ω :=
  integral_extDeriv_eq_boundaryIntegral ho hω (isClosed_closure.isCompact)

end ManifoldForm

end Polyfold
