import Polyfold.Chapter4.StokesFaceIntegral

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §4.4 (Theorem 4.4.7,
p. 199) and the proof of **Theorem 6.7.1** (p. 278): the boundary integral of a compact manifold
with corners split into the integrals over embedded ends and the integral over the rest of the
boundary, with no condition on the faces.

# The boundary integral with ends, without faces

`M` is a compact manifold modelled on `[0,∞)ⁿ⁺¹` with a continuous orientation `o`, and
`j a : N a → M` (`a` in a finite type) are maps of compact manifolds modelled on `[0,∞)ⁿ` which
read, in suitable charts of `M`, as coordinate face embeddings (`FaceChartPair`).  Nothing is
assumed on the other faces of `M`: they need not be embedded manifolds (a face may meet itself).

## The text, paraphrased

(p. 278) `∂S_F = S_0 ∪ S_1 ∪ S̃` with `S̃ ⊆ ∂X × (0, 1)`, and the integral over `∂S_F` is the sum
of the integrals over `S_0`, `S_1` and `S̃`, taking the orientations into account.

## What is formalized

* `EndRegion`: an open set `G` of a chart `e` of `M`, signed for `o`, in which the ends meeting
  `G` read as distinct coordinate faces `{x_{iₐ} = 0}` of `e` (every point of `G` on that
  coordinate face lies on the end), and every point of `G` with exactly one vanishing coordinate,
  not one of the `iₐ`, lies in a given set `L` (the lateral part of the boundary).
* `openFaceIntegral e i η`: the integral of `η` over the points of the face `{xᵢ = 0}` of `e` on
  no other face, the term `i` of the boundary integral in the chart `e`
  (`chartBoundaryIntegral_eq_sum_openFaceIntegral`).
* `EndRegion.sum_integral_eq`: the local identity
  `∑ₐ ∫_{N a} j_a^*η = orSign b · ∑_{i ∈ \{iₐ\}} faceSign i · ∫_{face i} η` for `η` supported
  in `G`.
* `tendsto_openFaceIntegral_smulFun`: dominated convergence on one face.
* **`tendsto_boundaryIntegral_smulFun`**: if every point has an end region, `cₘ : M → ℝ` are
  smooth with `|cₘ| ≤ 1`, `cₘ = 0` on the ends and `cₘ → 1` on `L`, then for every `C¹` form
  `ω`, `∫_{∂M} cₘ ω → ∫_{∂M} ω − ∑ₐ ∫_{N a} j_a^*ω`.  The limit is the integral of `ω` over the
  part of `∂M` in `L`, so `∫_{∂M} ω = ∑ₐ ∫_{N a} j_a^*ω + lim ∫_{∂M} cₘ ω`.
* `exists_endRegion`, **`tendsto_boundaryIntegral_levels`**: the case of the two level sets
  `τ = 0` and `τ = 1` of a smooth `τ : M → [0, 1]` with adapted face chart pairs, `L` the set
  `0 < τ < 1`, and `cₘ = χₘ ∘ τ` for cut-offs `χₘ` of `[0, 1]` vanishing at `0` and `1`
  (`exists_endCutoffs`: such cut-offs exist).
-/

open Set Filter Topology Manifold Module MeasureTheory

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- Mathlib's model with corners `[0,∞)ⁿ ⊆ ℝⁿ`. -/
local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

open ManifoldForm

section OpenFace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant (n + 1)) M]

/-- **The boundary term of the face `{xᵢ = 0}` of a chart** `e`: the integral of `ιᵢ^*(e⁻¹)^*η`
over the face parameters of the points of the face on no other face. -/
def openFaceIntegral (e : OpenPartialHomeomorph M (EuclideanQuadrant (n + 1))) (i : Fin (n + 1))
    (η : ManifoldForm (𝓠 (n + 1)) M n) : ℝ :=
  topFormIntegral (openFaceDomain e i) (facePullback i (chartForm (𝓠 (n + 1)) e η))

theorem chartBoundaryIntegral_eq_sum_openFaceIntegral
    (e : OpenPartialHomeomorph M (EuclideanQuadrant (n + 1))) (η : ManifoldForm (𝓠 (n + 1)) M n) :
    chartBoundaryIntegral e η = ∑ i, faceSign i * openFaceIntegral e i η :=
  chartBoundaryIntegral_eq_sum_openQuadrant e η

/-- The face integrand of `c η` is `c` (at the face point) times the face integrand of `η`. -/
theorem facePullback_smulFun_stdFrame (e : OpenPartialHomeomorph M (EuclideanQuadrant (n + 1)))
    (i : Fin (n + 1)) (c : M → ℝ) (η : ManifoldForm (𝓠 (n + 1)) M n)
    (z : EuclideanSpace ℝ (Fin n)) :
    facePullback i (chartForm (𝓠 (n + 1)) e (smulFun c η)) z (stdFrame n) =
      c (facePoint e i z) * facePullback i (chartForm (𝓠 (n + 1)) e η) z (stdFrame n) := by
  rw [facePullback_stdFrame, facePullback_stdFrame, chartForm_smulFun]
  rfl

/-- A face point where the face integrand of `η` does not vanish lies in the set outside which
`η` vanishes. -/
theorem facePoint_mem_of_ne_zero {η : ManifoldForm (𝓠 (n + 1)) M n} {K : Set M}
    (hη0 : ∀ x ∉ K, η x = 0) (e : OpenPartialHomeomorph M (EuclideanQuadrant (n + 1)))
    (i : Fin (n + 1)) {z : EuclideanSpace ℝ (Fin n)}
    (hne : facePullback i (chartForm (𝓠 (n + 1)) e η) z (stdFrame n) ≠ 0) :
    facePoint e i z ∈ K := by
  by_contra hK
  apply hne
  rw [facePullback_stdFrame, chartForm_eq_zero_of_notMem (y := faceEmbedding i z) hη0 e hK]
  rfl

variable [IsManifold (𝓠 (n + 1)) ∞ M]

/-- **The face integrand is integrable** over the open face, for a continuous form vanishing
outside a compact subset of the chart source. -/
theorem integrableOn_openFace {e : OpenPartialHomeomorph M (EuclideanQuadrant (n + 1))}
    (he : e ∈ IsManifold.maximalAtlas (𝓠 (n + 1)) ∞ M) {η : ManifoldForm (𝓠 (n + 1)) M n}
    (hη : ContMDiffForm (𝓠 (n + 1)) 0 η) {K : Set M} (hK : IsCompact K) (hKe : K ⊆ e.source)
    (hη0 : ∀ x ∉ K, η x = 0) (i : Fin (n + 1)) :
    IntegrableOn (fun z => facePullback i (chartForm (𝓠 (n + 1)) e η) z (stdFrame n))
      (openFaceDomain e i) := by
  set K' := e.extend (𝓠 (n + 1)) '' K
  have hK' : IsCompact K' :=
    hK.image_of_continuousOn (e.continuousOn_extend.mono (by rwa [e.extend_source]))
  have hK'T : K' ⊆ (e.extend (𝓠 (n + 1))).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (e.extend (𝓠 (n + 1))).map_source (by rw [e.extend_source]; exact hKe hx)
  set Kc := faceEmbedding i ⁻¹' K'
  have hKc : IsCompact Kc := by
    refine (hK'.image (faceProjection i).continuous).of_isClosed_subset
      (hK'.isClosed.preimage (faceEmbedding i).continuous) fun z hz => ?_
    exact ⟨_, hz, faceProjection_faceEmbedding i z⟩
  have hcont : ContinuousOn (fun z => facePullback i (chartForm (𝓠 (n + 1)) e η) z (stdFrame n))
      Kc := by
    have h1 : ContinuousOn (fun z => chartForm (𝓠 (n + 1)) e η (faceEmbedding i z)) Kc :=
      (hη.continuousOn_chartForm he).comp (faceEmbedding i).continuous.continuousOn
        fun z hz => hK'T hz
    refine ((ContinuousAlternatingMap.apply ℝ _ ℝ
      (i.removeNth (stdFrame (n + 1)))).continuous.comp_continuousOn h1).congr fun z _ => ?_
    exact facePullback_stdFrame i _ z
  refine IntegrableOn.of_forall_sdiff_eq_zero (hcont.integrableOn_compact hKc)
    (isOpen_openFaceDomain e i).measurableSet fun z hz => ?_
  by_contra hne
  have hzK := facePoint_mem_of_ne_zero hη0 e i hne
  apply hz.2
  change faceEmbedding i z ∈ K'
  rw [← extend_facePoint (openFaceDomain_subset e i hz.1)]
  exact mem_image_of_mem _ hzK

/-- **Dominated convergence on one open face**: if `cₘ` are continuous with `|cₘ| ≤ 1` and
`cₘ → 1` at the face points of the support, the face terms of `cₘ η` converge to that of `η`. -/
theorem tendsto_openFaceIntegral_smulFun
    {e : OpenPartialHomeomorph M (EuclideanQuadrant (n + 1))}
    (he : e ∈ IsManifold.maximalAtlas (𝓠 (n + 1)) ∞ M) {η : ManifoldForm (𝓠 (n + 1)) M n}
    (hη : ContMDiffForm (𝓠 (n + 1)) 0 η) {K : Set M} (hK : IsCompact K) (hKe : K ⊆ e.source)
    (hη0 : ∀ x ∉ K, η x = 0) (i : Fin (n + 1)) {c : ℕ → M → ℝ} (hc : ∀ m, Continuous (c m))
    (hc1 : ∀ m x, |c m x| ≤ 1)
    (hlim : ∀ z ∈ openFaceDomain e i, facePoint e i z ∈ K →
      Tendsto (fun m => c m (facePoint e i z)) atTop (𝓝 1)) :
    Tendsto (fun m => openFaceIntegral e i (smulFun (c m) η)) atTop
      (𝓝 (openFaceIntegral e i η)) := by
  set g := fun z => facePullback i (chartForm (𝓠 (n + 1)) e η) z (stdFrame n) with hg
  have hgi := integrableOn_openFace he hη hK hKe hη0 i
  have hfp : ContinuousOn (facePoint e i) (openFaceDomain e i) :=
    (e.continuousOn_extend_symm (I := 𝓠 (n + 1))).comp (faceEmbedding i).continuous.continuousOn
      fun z hz => openFaceDomain_subset e i hz
  have hmeas := (isOpen_openFaceDomain e i).measurableSet
  unfold openFaceIntegral topFormIntegral
  simp only [facePullback_smulFun_stdFrame]
  refine tendsto_integral_of_dominated_convergence (fun z => ‖g z‖) (fun m => ?_) hgi.norm
    (fun m => ?_) ?_
  · exact (((hc m).comp_continuousOn hfp).aestronglyMeasurable hmeas).mul hgi.aestronglyMeasurable
  · refine Eventually.of_forall fun z => ?_
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (by rw [Real.norm_eq_abs]; exact hc1 m _)
  · refine (ae_restrict_iff' hmeas).2 (Eventually.of_forall fun z hz => ?_)
    by_cases h0 : g z = 0
    · simp only [hg] at h0
      simp only [h0, mul_zero, tendsto_const_nhds]
    · have h := (hlim z hz (facePoint_mem_of_ne_zero hη0 e i h0)).mul_const (g z)
      rwa [one_mul] at h

end OpenFace

/-! ### End regions -/

section EndRegion

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant (n + 1)) M]
  {α : Type*} {N : α → Type*} [∀ a, TopologicalSpace (N a)]
  [∀ a, ChartedSpace (EuclideanQuadrant n) (N a)]

variable (o : TangentOrientation (𝓠 (n + 1)) M (n + 1)) (j : ∀ a, N a → M) (L : Set M)
  (e : OpenPartialHomeomorph M (EuclideanQuadrant (n + 1))) (G : Set M)

/-- **An end region** `G` of a chart `e` of `M` for the ends `j a : N a → M` and the lateral set
`L`: `o` reads in `e` on `G` as `orSign b` times the standard orientation; the ends meeting `G`
(a finite set `ends`) have face chart pairs `(e_{N a}, e, iₐ)` whose sources contain `j_a⁻¹(G)`,
with distinct coordinates `iₐ`; every point of `G` with `x_{iₐ} = 0` lies on the end `a`; and
every point of `G` with exactly one vanishing coordinate, which is none of the `iₐ`, lies in
`L`.  Unlike a good region (`GoodRegion`), nothing is said about the faces of `M` through the
points of `L`. -/
structure EndRegion where
  /-- The sign of `o` in `e` on `G`. -/
  sign : Bool
  orientationIn_eq : ∀ x ∈ G, orientationIn e x (o x) = signedOr sign (stdOrientation (n + 1))
  subset_source : G ⊆ e.source
  /-- The ends meeting `G`. -/
  ends : Finset α
  /-- Their face chart pairs. -/
  pair : ∀ a ∈ ends, FaceChartPair n (j a)
  pair_e : ∀ a (h : a ∈ ends), (pair a h).e = e
  src : ∀ a (h : a ∈ ends) (p : N a), j a p ∈ G → p ∈ (pair a h).eN.source
  miss : ∀ a ∉ ends, ∀ p : N a, j a p ∉ G
  inj : ∀ a (h : a ∈ ends) a' (h' : a' ∈ ends), (pair a h).i = (pair a' h').i → a = a'
  onEnd : ∀ a (h : a ∈ ends), ∀ x ∈ G, e.extend (𝓠 (n + 1)) x (pair a h).i = 0 →
    ∃ p, j a p = x
  lateral : ∀ x ∈ G, ∀ i : Fin (n + 1), e.extend (𝓠 (n + 1)) x i = 0 →
    (∀ l ≠ i, 0 < e.extend (𝓠 (n + 1)) x l) → (∀ a (h : a ∈ ends), (pair a h).i ≠ i) → x ∈ L

namespace EndRegion

variable {o j L e G} (g : EndRegion o j L e G)

open Classical in
/-- The coordinates `iₐ` of the ends meeting the region. -/
def endCoords : Finset (Fin (n + 1)) := g.ends.attach.image fun a => (g.pair a.1 a.2).i

theorem mem_endCoords {i : Fin (n + 1)} :
    i ∈ g.endCoords ↔ ∃ a, ∃ h : a ∈ g.ends, (g.pair a h).i = i := by
  classical
  simp only [endCoords, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]

variable {η : ManifoldForm (𝓠 (n + 1)) M n} {K : Set M}

/-- A point of the open face `iₐ` of `e` where the integrand of `η` (vanishing outside
`K ⊆ G`) does not vanish is `e_{N a}(p)`. -/
theorem exists_of_ne_zero (hKG : K ⊆ G) (hη0 : ∀ x ∉ K, η x = 0) (a : α) (ha : a ∈ g.ends)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ openFaceDomain e (g.pair a ha).i)
    (hne : facePullback (g.pair a ha).i (chartForm (𝓠 (n + 1)) e η) z ≠ 0) :
    ∃ p ∈ (g.pair a ha).eN.source, (g.pair a ha).eN.extend (𝓠 n) p = z := by
  set i := (g.pair a ha).i
  have hzD : z ∈ faceDomain e i := openFaceDomain_subset e i hz
  have hx : facePoint e i z ∈ K := by
    by_contra hK
    apply hne
    ext v
    rw [facePullback, formPullback_apply,
      chartForm_eq_zero_of_notMem (y := faceEmbedding i z) hη0 e hK]
    rfl
  have hxe := extend_facePoint hzD
  obtain ⟨p, hp⟩ := g.onEnd a ha _ (hKG hx) (by rw [hxe]; exact faceEmbedding_apply_self _ _)
  have hpP := g.src a ha p (hp ▸ hKG hx)
  have hext := (g.pair a ha).extend_eq p hpP
  rw [g.pair_e a ha, hp, hxe] at hext
  refine ⟨p, hpP, ?_⟩
  have := congrArg (faceProjection i) hext
  rwa [faceProjection_faceEmbedding, faceProjection_faceEmbedding, eq_comm] at this

/-- The boundary term of the face `iₐ` of `e` is the integral over the target of `e_{N a}`. -/
theorem openFaceIntegral_eq (hKG : K ⊆ G) (hη0 : ∀ x ∉ K, η x = 0) (a : α) (ha : a ∈ g.ends) :
    openFaceIntegral e (g.pair a ha).i η =
      topFormIntegral ((g.pair a ha).eN.extend (𝓠 n)).target
        (facePullback (g.pair a ha).i (chartForm (𝓠 (n + 1)) e η)) := by
  have hW : ((g.pair a ha).eN.extend (𝓠 n)).target ∩ openQuadrant univ ⊆
      openFaceDomain e (g.pair a ha).i := fun z hz => by
    have hp : ((g.pair a ha).eN.extend (𝓠 n)).symm z ∈ (g.pair a ha).eN.source := by
      rw [← (g.pair a ha).eN.extend_source (I := 𝓠 n)]
      exact ((g.pair a ha).eN.extend (𝓠 n)).map_target hz.1
    have h := (g.pair a ha).faceEmbedding_mem_target hp
    rw [((g.pair a ha).eN.extend (𝓠 n)).right_inv hz.1, g.pair_e a ha, e.extend_target] at h
    exact ⟨h.1, hz.2⟩
  rw [openFaceIntegral, topFormIntegral_eq_of_subset (isOpen_openFaceDomain e _).measurableSet hW
    fun z hz => by
      by_contra hne
      obtain ⟨p, hp, rfl⟩ := g.exists_of_ne_zero hKG hη0 a ha hz.1 hne
      exact hz.2 ⟨PartialEquiv.map_source _
        (by rw [OpenPartialHomeomorph.extend_source]; exact hp), hz.1.2⟩]
  unfold topFormIntegral
  refine setIntegral_congr_set ?_
  have hsub : ((g.pair a ha).eN.extend (𝓠 n)).target ⊆ closedQuadrant univ := by
    rw [← range_modelWithCornersEuclideanQuadrant]
    exact (g.pair a ha).eN.extend_target_subset_range
  have h := (EventuallyEq.refl (ae volume) ((g.pair a ha).eN.extend (𝓠 n)).target).inter
    (openQuadrant_ae_eq_quadrant (S := univ))
  rwa [inter_eq_left.2 hsub] at h

/-- On the face `iₐ` the form `c η` has zero boundary term if `c` vanishes on the end `a`. -/
theorem openFaceIntegral_smulFun_eq_zero (hKG : K ⊆ G) (hη0 : ∀ x ∉ K, η x = 0) (a : α)
    (ha : a ∈ g.ends) {c : M → ℝ} (hc : ∀ p, c (j a p) = 0) :
    openFaceIntegral e (g.pair a ha).i (smulFun c η) = 0 := by
  unfold openFaceIntegral topFormIntegral
  refine setIntegral_eq_zero_of_forall_eq_zero fun z hz => ?_
  rw [facePullback_smulFun_stdFrame]
  by_cases hne : facePullback (g.pair a ha).i (chartForm (𝓠 (n + 1)) e η) z = 0
  · rw [hne]; simp
  obtain ⟨p, hp, rfl⟩ := g.exists_of_ne_zero hKG hη0 a ha hz hne
  have hzt : (g.pair a ha).eN.extend (𝓠 n) p ∈ ((g.pair a ha).eN.extend (𝓠 n)).target :=
    ((g.pair a ha).eN.extend (𝓠 n)).map_source
      (by rw [OpenPartialHomeomorph.extend_source]; exact hp)
  have hfp : facePoint e (g.pair a ha).i ((g.pair a ha).eN.extend (𝓠 n) p) = j a p := by
    have h := (g.pair a ha).symm_eq hzt
    rw [g.pair_e a ha, (g.pair a ha).eN.extend_left_inv hp] at h
    exact h
  rw [hfp, hc, zero_mul]

/-- Points of an open face with no end coordinate, in the support, lie in `L`. -/
theorem facePoint_mem_lateral (hKG : K ⊆ G) {i : Fin (n + 1)} (hi : i ∉ g.endCoords)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ openFaceDomain e i) (hzK : facePoint e i z ∈ K) :
    facePoint e i z ∈ L := by
  have hxe := extend_facePoint (openFaceDomain_subset e i hz)
  refine g.lateral _ (hKG hzK) i (by rw [hxe]; exact faceEmbedding_apply_self _ _)
    (fun l hl => ?_) fun a ha h => hi ((g.mem_endCoords).2 ⟨a, ha, h⟩)
  rw [hxe]
  have h0 : faceEmbedding i z l ≠ 0 := fun h => hl ((faceEmbedding_eq_zero_iff hz l).1 h)
  have hnn : 0 ≤ faceEmbedding i z l := by
    have h' := e.extend_target_subset_range (I := 𝓠 (n + 1)) (openFaceDomain_subset e i hz)
    rw [range_modelWithCornersEuclideanQuadrant] at h'
    exact h' l (mem_univ l)
  exact lt_of_le_of_ne hnn (Ne.symm h0)

variable [IsManifold (𝓠 (n + 1)) ∞ M] [∀ a, IsManifold (𝓠 n) ∞ (N a)] [T2Space M]
  [∀ a, T2Space (N a)] [∀ a, CompactSpace (N a)] (hj : ∀ a, Continuous (j a))
  (hcover : ∀ a (p : N a), ∃ P : FaceChartPair n (j a), p ∈ P.eN.source)
  {oN : ∀ a, TangentOrientation (𝓠 n) (N a) n} (hoN : ∀ a, IsInducedOrientation (j a) o (oN a))
  (hoNc : ∀ a, (oN a).IsContinuous (𝓠 n) ∞)
include hj hcover hoN hoNc

/-- The integral over the end `a` of a form supported in `G` is `orSign b · faceSign iₐ` times
the integral of its expression over the face chart target. -/
theorem integral_restrictForm_eq (hη : ContMDiffForm (𝓠 (n + 1)) 0 η) (hK : IsCompact K)
    (hKG : K ⊆ G) (hη0 : ∀ x ∉ K, η x = 0) (a : α) (ha : a ∈ g.ends) :
    integral (oN a) (restrictForm (j a) η) = orSign g.sign * faceSign (g.pair a ha).i *
      topFormIntegral ((g.pair a ha).eN.extend (𝓠 n)).target
        (facePullback (g.pair a ha).i (chartForm (𝓠 (n + 1)) e η)) := by
  have hb : ∀ p ∈ (g.pair a ha).eN.source ∩ j a ⁻¹' G,
      orientationIn (g.pair a ha).eN p (oN a p) =
        signedOr (g.sign == faceBool (g.pair a ha).i) (stdOrientation n) := fun p hp => by
    rw [hoN a (g.pair a ha) p hp.1, (g.pair a ha).boundarySign_eq o (b := g.sign)]
    rw [g.pair_e a ha]
    exact g.orientationIn_eq _ hp.2
  have hK' : IsCompact (j a ⁻¹' K) := (hK.isClosed.preimage (hj a)).isCompact
  rw [integral_eq_chartIntegral_of_mem_maximalAtlas (hoNc a)
    (contMDiffForm_restrictForm (hj a) (hcover a) hη) (g.pair a ha).mem_N inter_subset_left hb
    hK' (fun p hp => ⟨g.src a ha p (hKG hp), hKG hp⟩)
    (fun p hp => restrictForm_eq_zero _ (hη0 _ hp)), orSign_beq, orSign_faceBool, chartIntegral,
    topFormIntegral_congr (measurableSet_extend_target (g.pair a ha).eN)
      fun z hz => (g.pair a ha).chartForm_restrictForm (hj a) η hz, g.pair_e a ha]
  rfl

/-- **The local identity of an end region**: for a continuous `n`-form `η` vanishing outside a
compact subset of `G`, `∑ₐ ∫_{N a} j_a^*η = orSign b · ∑_{i ∈ \{iₐ\}} faceSign i ∫_{face i} η`. -/
theorem sum_integral_eq [Fintype α] (hη : ContMDiffForm (𝓠 (n + 1)) 0 η) (hK : IsCompact K)
    (hKG : K ⊆ G) (hη0 : ∀ x ∉ K, η x = 0) :
    ∑ a, integral (oN a) (restrictForm (j a) η) =
      orSign g.sign * ∑ i ∈ g.endCoords, faceSign i * openFaceIntegral e i η := by
  classical
  have hsplit : ∑ a, integral (oN a) (restrictForm (j a) η) =
      ∑ a ∈ g.ends, integral (oN a) (restrictForm (j a) η) :=
    (Finset.sum_subset (Finset.subset_univ _) fun a _ ha => integral_eq_zero fun p =>
      restrictForm_eq_zero _ (hη0 _ fun hpK => g.miss a ha p (hKG hpK))).symm
  have hterm : ∀ a : g.ends, integral (oN a) (restrictForm (j a) η) =
      orSign g.sign * (faceSign (g.pair a.1 a.2).i * openFaceIntegral e (g.pair a.1 a.2).i η) :=
    fun a => by
      rw [g.integral_restrictForm_eq hj hcover hoN hoNc hη hK hKG hη0 a.1 a.2,
        g.openFaceIntegral_eq hKG hη0 a.1 a.2, mul_assoc]
  have hinj : Set.InjOn (fun a : g.ends => (g.pair a.1 a.2).i) g.ends.attach := by
    intro a _ a' _ h
    exact Subtype.ext (g.inj _ _ _ _ h)
  rw [hsplit, ← Finset.sum_attach, Finset.sum_congr rfl fun a _ => hterm a, ← Finset.mul_sum,
    endCoords, Finset.sum_image hinj]

end EndRegion

/-! ### The boundary integral with ends -/

variable [IsManifold (𝓠 (n + 1)) ∞ M] [∀ a, IsManifold (𝓠 n) ∞ (N a)] [T2Space M]
  [CompactSpace M] [∀ a, T2Space (N a)] [∀ a, CompactSpace (N a)] [Fintype α]

omit [IsManifold (𝓠 (n + 1)) ∞ M] [T2Space M] [∀ a, IsManifold (𝓠 n) ∞ (N a)]
  [∀ a, T2Space (N a)] [∀ a, CompactSpace (N a)] [Fintype α] [CompactSpace M] in
/-- Every point of an end lies in the source of a face chart pair (that of its end region). -/
theorem exists_faceChartPair_of_endRegion {G : M → Set M} (hxG : ∀ x, x ∈ G x)
    (reg : ∀ x, EndRegion o j L (chartAt (EuclideanQuadrant (n + 1)) x) (G x)) (a : α)
    (p : N a) : ∃ P : FaceChartPair n (j a), p ∈ P.eN.source := by
  have ha : a ∈ (reg (j a p)).ends := by
    by_contra h
    exact (reg (j a p)).miss a h p (hxG _)
  exact ⟨(reg (j a p)).pair a ha, (reg (j a p)).src a ha p (hxG _)⟩

/-- **The boundary integral with ends, without faces** (2021, proof of Theorem 6.7.1, p. 278,
with Theorem 4.4.7, p. 199): if every point of the compact `M` has an end region for the ends
`j a : N a → M` (compact, with the induced orientations `o_N a`) and the lateral set `L`, and
`cₘ : M → ℝ` are smooth with `|cₘ| ≤ 1`, `cₘ = 0` on the ends and `cₘ → 1` pointwise on `L`,
then for every `C¹` `n`-form `ω`
`∫_{∂M} cₘ ω → ∫_{∂M} ω − ∑ₐ ∫_{N a} j_a^*ω`:
the boundary integral is the sum of the integrals over the ends and of the integral over the
part of the boundary in `L` (the limit). -/
theorem tendsto_boundaryIntegral_smulFun (ho : o.IsContinuous (𝓠 (n + 1)) ∞)
    (hj : ∀ a, Continuous (j a)) {oN : ∀ a, TangentOrientation (𝓠 n) (N a) n}
    (hoN : ∀ a, IsInducedOrientation (j a) o (oN a)) (hoNc : ∀ a, (oN a).IsContinuous (𝓠 n) ∞)
    (G : M → Set M) (hGo : ∀ x, IsOpen (G x)) (hxG : ∀ x, x ∈ G x)
    (reg : ∀ x, EndRegion o j L (chartAt (EuclideanQuadrant (n + 1)) x) (G x))
    {c : ℕ → M → ℝ} (hcs : ∀ m, ContMDiff (𝓠 (n + 1)) 𝓘(ℝ) ∞ (c m))
    (hc1 : ∀ m x, |c m x| ≤ 1) (hc0 : ∀ m a p, c m (j a p) = 0)
    (hcL : ∀ x ∈ L, Tendsto (fun m => c m x) atTop (𝓝 1))
    {ω : ManifoldForm (𝓠 (n + 1)) M n} (hω : ContMDiffForm (𝓠 (n + 1)) 1 ω) :
    Tendsto (fun m => boundaryIntegral o (smulFun (c m) ω)) atTop
      (𝓝 (boundaryIntegral o ω - ∑ a, integral (oN a) (restrictForm (j a) ω))) := by
  classical
  have hcover := exists_faceChartPair_of_endRegion o j L hxG reg
  have hc : IsCompact (tsupport ω) := isClosed_closure.isCompact
  obtain ⟨T, D, hD⟩ := exists_integrationData_of_regions (o := o) hc G hGo hxG
    (fun x => (reg x).subset_source) (fun x => (reg x).sign) (fun x => (reg x).orientationIn_eq)
  have hω0 : ∀ x ∉ tsupport ω, ω x = 0 := fun x hx => eq_zero_of_notMem_tsupport hx
  have hcm : ∀ m, ContMDiffForm (𝓠 (n + 1)) 1 (smulFun (c m) ω) := fun m =>
    ContMDiffForm.smulFun (by norm_cast) ((hcs m).of_le (by exact_mod_cast le_top)) hω
  have hsupp : ∀ m, tsupport (smulFun (c m) ω) ⊆ tsupport ω := fun m =>
    (tsupport_smulFun_subset _ _).trans inter_subset_right
  -- the charts, regions and supports of the integration data
  have hC0 : ∀ k, ContMDiffForm (𝓠 (n + 1)) 0 (smulFun (D.ρ k) ω) := fun k =>
    D.contMDiffForm_smulFun (by simp) k (hω.of_le zero_le_one)
  have hKk : ∀ k, IsCompact (_root_.tsupport (D.ρ k) ∩ tsupport ω) := fun k =>
    hc.inter_left (isClosed_tsupport (D.ρ k))
  have hKG : ∀ k, _root_.tsupport (D.ρ k) ∩ tsupport ω ⊆ G k.1 := fun k x hx =>
    (hD k).2.1 ▸ D.tsupport_subset k hx.1
  have hη0 : ∀ k, ∀ x ∉ _root_.tsupport (D.ρ k) ∩ tsupport ω, smulFun (D.ρ k) ω x = 0 :=
    fun k x hx => smulFun_eq_zero_of_notMem hω0 hx
  have hchart : ∀ k, D.chart k = chartAt (EuclideanQuadrant (n + 1)) k.1 := fun k => by
    rw [IntegrationData.chart, (hD k).1]
  have hsign : ∀ k, D.sign k = (reg k.1).sign := fun k => (hD k).2.2
  have hmax : ∀ k : {x // x ∈ T}, chartAt (EuclideanQuadrant (n + 1)) k.1 ∈
      IsManifold.maximalAtlas (𝓠 (n + 1)) ∞ M := fun k => IsManifold.chart_mem_maximalAtlas _
  have hKe : ∀ k, _root_.tsupport (D.ρ k) ∩ tsupport ω ⊆
      (chartAt (EuclideanQuadrant (n + 1)) k.1).source := fun k =>
    (hKG k).trans (reg k.1).subset_source
  -- the boundary integrals with respect to `D`
  have hcomm : ∀ m k, smulFun (D.ρ k) (smulFun (c m) ω) = smulFun (c m) (smulFun (D.ρ k) ω) :=
    fun m k => by
      funext x
      simp only [smulFun_apply, smul_smul, mul_comm]
  set E := fun k : {x // x ∈ T} => (reg k.1).endCoords
  set Lat : ℝ := ∑ k, orSign (D.sign k) * ∑ i ∈ (E k)ᶜ, faceSign i *
    openFaceIntegral (chartAt (EuclideanQuadrant (n + 1)) k.1) i (smulFun (D.ρ k) ω)
  have hlhs : ∀ m, boundaryIntegral o (smulFun (c m) ω) =
      ∑ k, orSign (D.sign k) * ∑ i ∈ (E k)ᶜ, faceSign i *
        openFaceIntegral (chartAt (EuclideanQuadrant (n + 1)) k.1) i
          (smulFun (c m) (smulFun (D.ρ k) ω)) := fun m => by
    rw [boundaryIntegral_eq_integrationData ho (hcm m) (hc.of_isClosed_subset isClosed_closure
      (hsupp m)) D (hsupp m), IntegrationData.boundaryIntegral]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcomm, hchart, chartBoundaryIntegral_eq_sum_openFaceIntegral,
      ← Finset.sum_add_sum_compl (E k)]
    have h0 : ∑ i ∈ E k, faceSign i * openFaceIntegral (chartAt (EuclideanQuadrant (n + 1)) k.1) i
        (smulFun (c m) (smulFun (D.ρ k) ω)) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      obtain ⟨a, ha, rfl⟩ := ((reg k.1).mem_endCoords).1 hi
      rw [(reg k.1).openFaceIntegral_smulFun_eq_zero (hKG k) (hη0 k) a ha (hc0 m a), mul_zero]
    rw [h0, zero_add]
  have hrhs : boundaryIntegral o ω - ∑ a, integral (oN a) (restrictForm (j a) ω) = Lat := by
    have hlin : ∀ a, integral (oN a) (restrictForm (j a) ω) =
        ∑ k, integral (oN a) (restrictForm (j a) (smulFun (D.ρ k) ω)) := fun a => by
      have hs := finsetSum_smulFun_eq_self Finset.univ D.sum_eq_one subset_rfl hω0
      conv_lhs => rw [← hs, restrictForm_finsetSum]
      exact integral_finsetSum (hoNc a) Finset.univ
        (fun k _ => contMDiffForm_restrictForm (hj a) (hcover a) (hC0 k))
        (fun k _ => isClosed_closure.isCompact)
    rw [boundaryIntegral_eq_integrationData ho hω hc D subset_rfl, IntegrationData.boundaryIntegral,
      Finset.sum_congr rfl fun a _ => hlin a, Finset.sum_comm, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(reg k.1).sum_integral_eq hj hcover hoN hoNc (hC0 k) (hKk k) (hKG k) (hη0 k), hchart,
      chartBoundaryIntegral_eq_sum_openFaceIntegral, ← Finset.sum_add_sum_compl (E k), hsign]
    ring
  rw [hrhs]
  simp only [hlhs]
  refine tendsto_finsetSum _ fun k _ => (tendsto_finsetSum _ fun i hi => ?_).const_mul _
  refine (tendsto_openFaceIntegral_smulFun (hmax k) (hC0 k) (hKk k) (hKe k) (hη0 k) i
    (fun m => (hcs m).continuous) hc1 fun z hz hzK => hcL _ ?_).const_mul _
  exact (reg k.1).facePoint_mem_lateral (hKG k) (Finset.mem_compl.1 hi) hz hzK

end EndRegion

/-! ### Two ends at the levels `0` and `1` of a function -/

section Levels

/-- The level `0` (for `false`) or `1` (for `true`) of an end. -/
def endLevel (b : Bool) : ℝ := if b then 1 else 0

theorem abs_endLevel_sub_of_ne {a b : Bool} (h : a ≠ b) : |endLevel a - endLevel b| = 1 := by
  cases a <;> cases b <;> simp_all [endLevel]

variable {M : Type*} [TopologicalSpace M] {N : Bool → Type*} [∀ b, TopologicalSpace (N b)]


/-- **The end `j b` is adapted** at each of its points `p`: there are a face chart pair
`(e_N, e, i)` of `j b` with `e = chartAt (j b p)` and an open neighbourhood `B` of `j b p` in the
source of `e` on which `range (j b)` is the coordinate face `\{xᵢ = 0\}` of `e`, with
`j_b⁻¹(B)` in the source of `e_N`. -/
def IsAdaptedEnd (n : ℕ) [∀ b, ChartedSpace (EuclideanQuadrant n) (N b)]
    [ChartedSpace (EuclideanQuadrant (n + 1)) M] (j : ∀ b, N b → M) (b : Bool) : Prop :=
  ∀ p : N b, ∃ P : FaceChartPair n (j b), P.e = chartAt (EuclideanQuadrant (n + 1)) (j b p) ∧
    ∃ B : Set M, IsOpen B ∧ j b p ∈ B ∧
      B ⊆ (chartAt (EuclideanQuadrant (n + 1)) (j b p)).source ∧
      (∀ y ∈ B, y ∈ range (j b) ↔
        (chartAt (EuclideanQuadrant (n + 1)) (j b p)).extend (𝓠 (n + 1)) y P.i = 0) ∧
      ∀ q, j b q ∈ B → q ∈ P.eN.source

omit [TopologicalSpace M] [∀ b, TopologicalSpace (N b)] in
theorem endLevel_of_mem_range {j : ∀ b, N b → M} {τ : M → ℝ}
    (hrange : ∀ b, range (j b) = τ ⁻¹' {endLevel b}) (b : Bool)
    (p : N b) : τ (j b p) = endLevel b := by
  have h : j b p ∈ τ ⁻¹' {endLevel b} := hrange b ▸ mem_range_self p
  exact h

variable {n : ℕ} [ChartedSpace (EuclideanQuadrant (n + 1)) M] [IsManifold (𝓠 (n + 1)) ∞ M]
  [∀ b, ChartedSpace (EuclideanQuadrant n) (N b)]
  {o : TangentOrientation (𝓠 (n + 1)) M (n + 1)} {j : ∀ b, N b → M} {τ : M → ℝ}

/-- **Every point has an end region** for the two ends `τ = 0`, `τ = 1` and the lateral set
`0 < τ < 1`: near a point of the end `b`, the adapted neighbourhood intersected with the points
where `o` reads as at the point and with `|τ − b| < 1/2`; elsewhere, the chart source
intersected with these points and with `0 < τ < 1`. -/
theorem exists_endRegion (ho : o.IsContinuous (𝓠 (n + 1)) ∞) (hτ : Continuous τ)
    (hτ01 : ∀ x, τ x ∈ Icc (0 : ℝ) 1) (hrange : ∀ b, range (j b) = τ ⁻¹' {endLevel b})
    (hadapt : ∀ b, IsAdaptedEnd n j b) (x : M) :
    ∃ G : Set M, IsOpen G ∧ x ∈ G ∧
      Nonempty (EndRegion o j (τ ⁻¹' Ioo 0 1) (chartAt (EuclideanQuadrant (n + 1)) x) G) := by
  classical
  set e := chartAt (EuclideanQuadrant (n + 1)) x with he_def
  set S := {y | y ∈ e.source ∧ orientationIn e y (o y) = orientationIn e x (o x)} with hS_def
  have hSo : IsOpen S := by
    refine isOpen_iff_mem_nhds.2 fun y hy => ?_
    filter_upwards [e.open_source.mem_nhds hy.1,
      ho e (IsManifold.chart_mem_maximalAtlas x) y hy.1] with z hz hz'
    exact ⟨hz, hz'.trans hy.2⟩
  have hxS : x ∈ S := ⟨mem_chart_source _ x, rfl⟩
  have hsignS : ∀ y ∈ S, orientationIn e y (o y) = signedOr
      (decide (orientationIn e x (o x) = stdOrientation (n + 1))) (stdOrientation (n + 1)) :=
    fun y hy => hy.2.trans (eq_signedOr_decide _)
  by_cases h : ∃ b, ∃ p : N b, j b p = x
  · obtain ⟨b, p, hpx⟩ := h
    obtain ⟨P, hPe, B, hBo, hpB, hBs, hBiff, hBsrc⟩ := hadapt b p
    rw [hpx] at hPe hpB hBs hBiff
    have hex : ∀ a (h : a ∈ ({b} : Finset Bool)), ∃ Q : FaceChartPair n (j a), Q.e = e ∧
        (∀ y ∈ B, y ∈ range (j a) ↔ e.extend (𝓠 (n + 1)) y Q.i = 0) ∧
        ∀ q, j a q ∈ B → q ∈ Q.eN.source := fun a h => by
      obtain rfl := Finset.mem_singleton.1 h
      exact ⟨P, hPe, hBiff, hBsrc⟩
    set G := B ∩ S ∩ {y | |τ y - endLevel b| < 1 / 2}
    have hGo : IsOpen G := (hBo.inter hSo).inter
      (isOpen_lt ((hτ.sub continuous_const).abs) continuous_const)
    have hxG : x ∈ G := ⟨⟨hpB, hxS⟩, by
      change |τ x - endLevel b| < 1 / 2
      rw [← hpx, endLevel_of_mem_range hrange b p, sub_self, abs_zero]
      norm_num⟩
    refine ⟨G, hGo, hxG, ⟨{
      sign := decide (orientationIn e x (o x) = stdOrientation (n + 1))
      orientationIn_eq := fun y hy => hsignS y hy.1.2
      subset_source := fun y hy => hBs hy.1.1
      ends := {b}
      pair := fun a h => (hex a h).choose
      pair_e := fun a h => (hex a h).choose_spec.1
      src := fun a h q hq => (hex a h).choose_spec.2.2 q hq.1.1
      miss := fun a ha q hq => by
        have hab : a ≠ b := fun h => ha (Finset.mem_singleton.2 h)
        have h1 := hq.2
        change |τ (j a q) - endLevel b| < 1 / 2 at h1
        rw [endLevel_of_mem_range hrange a q, abs_endLevel_sub_of_ne hab] at h1
        norm_num at h1
      inj := fun a h a' h' _ => (Finset.mem_singleton.1 h).trans (Finset.mem_singleton.1 h').symm
      onEnd := fun a h y hy hy0 => ((hex a h).choose_spec.2.1 y hy.1.1).2 hy0
      lateral := fun y hy i _ hpos hne => by
        have hb : b ∈ ({b} : Finset Bool) := Finset.mem_singleton_self b
        have hpi := hpos _ (hne b hb)
        have hnot : y ∉ range (j b) := fun hy' =>
          (ne_of_gt hpi) (((hex b hb).choose_spec.2.1 y hy.1.1).1 hy')
        have hne1 : τ y ≠ endLevel b := fun h' => hnot (by rw [hrange b]; exact h')
        have h1 := hy.2
        change |τ y - endLevel b| < 1 / 2 at h1
        have h01 := hτ01 y
        have hne2 : τ y ≠ endLevel (!b) := fun h' => by
          rw [h', abs_endLevel_sub_of_ne (by cases b <;> simp)] at h1
          norm_num at h1
        have hn0 : τ y ≠ 0 := by cases b <;> simp [endLevel] at hne1 hne2 <;> assumption
        have hn1 : τ y ≠ 1 := by cases b <;> simp [endLevel] at hne1 hne2 <;> assumption
        exact ⟨lt_of_le_of_ne h01.1 (Ne.symm hn0), lt_of_le_of_ne h01.2 hn1⟩ }⟩⟩
  · simp only [not_exists] at h
    have hx01 : τ x ∈ Ioo (0 : ℝ) 1 := by
      have h01 := hτ01 x
      have hne : ∀ b, τ x ≠ endLevel b := fun b hb => by
        have : x ∈ range (j b) := by rw [hrange b]; exact hb
        obtain ⟨p, hp⟩ := this
        exact h b p hp
      exact ⟨lt_of_le_of_ne h01.1 (Ne.symm (by simpa [endLevel] using hne false)),
        lt_of_le_of_ne h01.2 (by simpa [endLevel] using hne true)⟩
    set G := S ∩ τ ⁻¹' Ioo 0 1
    refine ⟨G, hSo.inter (isOpen_Ioo.preimage hτ), ⟨hxS, hx01⟩, ⟨{
      sign := decide (orientationIn e x (o x) = stdOrientation (n + 1))
      orientationIn_eq := fun y hy => hsignS y hy.1
      subset_source := fun y hy => hy.1.1
      ends := ∅
      pair := fun a h => absurd h (Finset.notMem_empty a)
      pair_e := fun a h => absurd h (Finset.notMem_empty a)
      src := fun a h => absurd h (Finset.notMem_empty a)
      miss := fun a _ q hq => by
        have h1 := hq.2
        rw [mem_preimage, endLevel_of_mem_range hrange a q] at h1
        cases a <;> simp [endLevel] at h1
      inj := fun a h => absurd h (Finset.notMem_empty a)
      onEnd := fun a h => absurd h (Finset.notMem_empty a)
      lateral := fun y hy _ _ _ _ => hy.2 }⟩⟩

variable [T2Space M] [CompactSpace M] [∀ b, IsManifold (𝓠 n) ∞ (N b)] [∀ b, T2Space (N b)]
  [∀ b, CompactSpace (N b)]

/-- **The boundary integral of a manifold with two ends at the levels of a function**
(2021, proof of Theorem 6.7.1, p. 278): let `τ : M → [0, 1]` be smooth on the compact `M`, the
ends `j b : N b → M` (compact, with the induced orientations `o_N b`) the level sets
`τ = 0`, `τ = 1`, adapted (`IsAdaptedEnd`), and let `χₘ` be smooth cut-offs with `|χₘ| ≤ 1`,
`χₘ(0) = χₘ(1) = 0` and `χₘ → 1` on `(0, 1)`.  Then for every `C¹` form `ω`,
`∫_{∂M} (χₘ ∘ τ) ω → ∫_{∂M} ω − ∑_b ∫_{N b} j_b^*ω`: the limit is the integral of `ω` over the
part of `∂M` with `0 < τ < 1`.  No condition is put on the faces of `M`. -/
theorem tendsto_boundaryIntegral_levels (ho : o.IsContinuous (𝓠 (n + 1)) ∞)
    (hj : ∀ b, Continuous (j b)) {oN : ∀ b, TangentOrientation (𝓠 n) (N b) n}
    (hoN : ∀ b, IsInducedOrientation (j b) o (oN b)) (hoNc : ∀ b, (oN b).IsContinuous (𝓠 n) ∞)
    (hτs : ContMDiff (𝓠 (n + 1)) 𝓘(ℝ) ∞ τ) (hτ01 : ∀ x, τ x ∈ Icc (0 : ℝ) 1)
    (hrange : ∀ b, range (j b) = τ ⁻¹' {endLevel b}) (hadapt : ∀ b, IsAdaptedEnd n j b)
    {χ : ℕ → ℝ → ℝ} (hχs : ∀ m, ContDiff ℝ ∞ (χ m)) (hχ1 : ∀ m t, |χ m t| ≤ 1)
    (hχ0 : ∀ m, χ m 0 = 0) (hχ1' : ∀ m, χ m 1 = 0)
    (hχ : ∀ t ∈ Ioo (0 : ℝ) 1, Tendsto (fun m => χ m t) atTop (𝓝 1))
    {ω : ManifoldForm (𝓠 (n + 1)) M n} (hω : ContMDiffForm (𝓠 (n + 1)) 1 ω) :
    Tendsto (fun m => boundaryIntegral o (smulFun (fun x => χ m (τ x)) ω)) atTop
      (𝓝 (boundaryIntegral o ω - ∑ b, integral (oN b) (restrictForm (j b) ω))) := by
  choose G hGo hxG hreg using exists_endRegion ho hτs.continuous hτ01 hrange hadapt
  refine tendsto_boundaryIntegral_smulFun o j (τ ⁻¹' Ioo 0 1) ho hj hoN hoNc G hGo hxG
    (fun x => (hreg x).some) (fun m => (hχs m).comp_contMDiff hτs) (fun m x => hχ1 m _)
    (fun m b p => ?_) (fun x hx => hχ _ hx) hω
  change χ m (τ (j b p)) = 0
  rw [endLevel_of_mem_range hrange b p]
  cases b
  · exact hχ0 m
  · exact hχ1' m

end Levels

/-- **Cut-offs of `[0, 1]` vanishing at the ends**: `χₘ(t) = ψ((m+1)t) ψ((m+1)(1−t))`, `ψ` the
smooth transition function, is smooth, takes values in `[0, 1]`, vanishes at `0` and `1`, and
tends to `1` at every `t ∈ (0, 1)`. -/
theorem exists_endCutoffs : ∃ χ : ℕ → ℝ → ℝ, (∀ m, ContDiff ℝ ∞ (χ m)) ∧
    (∀ m t, |χ m t| ≤ 1) ∧ (∀ m, χ m 0 = 0) ∧ (∀ m, χ m 1 = 0) ∧
    ∀ t ∈ Ioo (0 : ℝ) 1, Tendsto (fun m => χ m t) atTop (𝓝 1) := by
  refine ⟨fun m t => Real.smoothTransition (((m : ℝ) + 1) * t) *
    Real.smoothTransition (((m : ℝ) + 1) * (1 - t)), fun m => ?_, fun m t => ?_, fun m => ?_,
    fun m => ?_, fun t ht => ?_⟩
  · exact (Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id)).mul
      (Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_id)))
  · rw [abs_of_nonneg (mul_nonneg (Real.smoothTransition.nonneg _)
      (Real.smoothTransition.nonneg _))]
    exact mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
      (Real.smoothTransition.le_one _)
  · simp [Real.smoothTransition.zero_of_nonpos le_rfl]
  · simp [Real.smoothTransition.zero_of_nonpos le_rfl]
  · obtain ⟨m₀, hm₀⟩ := exists_nat_ge (max (1 / t) (1 / (1 - t)))
    have ht1 : 0 < 1 - t := by linarith [ht.2]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop m₀] with m hm
    have hm' : (max (1 / t) (1 / (1 - t)) : ℝ) ≤ (m : ℝ) + 1 :=
      hm₀.trans ((Nat.cast_le.2 hm).trans (by linarith))
    have h1 : 1 ≤ ((m : ℝ) + 1) * t := by
      have := (le_max_left _ _).trans hm'
      rw [div_le_iff₀ ht.1] at this
      linarith
    have h2 : 1 ≤ ((m : ℝ) + 1) * (1 - t) := by
      have := (le_max_right _ _).trans hm'
      rw [div_le_iff₀ ht1] at this
      linarith
    rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2, mul_one]

end Polyfold
