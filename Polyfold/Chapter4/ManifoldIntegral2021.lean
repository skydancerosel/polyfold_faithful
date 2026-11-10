import Polyfold.Chapter4.ManifoldForms2021
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021): the integral of a
top-degree form over an oriented finite-dimensional manifold with boundary with corners, used in
**Theorem 4.4.7** (p. 199; preprint Theorem 4.28, Stokes' theorem, gap G.40) and
**Theorem 6.7.1** (p. 277).  Numbers and pages are the 2021 text's.

# The integral of a top-degree form over an oriented manifold with corners

`M` is a `C^∞` manifold modelled on Mathlib's `modelWithCornersEuclideanQuadrant n`
(`𝓠 n`, the quadrant `[0,∞)ⁿ` in `ℝⁿ = EuclideanSpace ℝ (Fin n)`, the model of the project's
solution sets, `Chapter9/MathlibSolutionSets.lean`), with a continuous tangent orientation `o`
(`TangentOrientation.IsContinuous`, `Chapter6/ManifoldOrientation.lean`; an oriented atlas gives
one, `IsOrientedAtlas.isContinuous_tangentOrientation`).  `ℝⁿ` carries its standard orientation
`stdOrientation n`.

## What is formalized

* `chartIntegral e ω`: the integral `∫_{e(U)} (e⁻¹)^*ω` of the expression of an `n`-form in a
  chart, over the chart target (`topFormIntegral`, `EuclideanForms2021.lean`).
* **Change of charts** (`chartIntegral_eq_integral_sign`, `_of_det_pos`, `_signed`): for a form
  vanishing outside `K ⊆ e.source ∩ e'.source`, the integral in `e'` is the integral in `e` of
  `sign det D(e' ∘ e⁻¹) · (e⁻¹)^*ω`; for charts in which `o` reads as `±` the standard
  orientation (`signedOr`), the signed chart integrals agree.  In dimension `1` the quadrant model
  forces charts that reverse the orientation at some boundary points (`[0, 1]` has no oriented
  atlas, `ManifoldOrientation.lean`), so charts carry a sign.
* `IntegrationData M o s ι`: a finite family of charts `chartAt H cⱼ` with regions `Vⱼ` on which
  `o` reads as `signedOr bⱼ (stdOrientation n)`, and smooth functions `ρⱼ` with
  `tsupport ρⱼ ⊆ Vⱼ` and `∑ ρⱼ = 1` on `s` (a smooth partition of unity on `s` subordinate to
  signed charts).  `IntegrationData.integral D ω = ∑ⱼ ±ⱼ ∫_{cⱼ} ρⱼ ω`.
* **Independence** (`IntegrationData.integral_eq`): two such data give the same integral for a
  continuous form vanishing outside a compact subset of both `s`; the integral is linear
  (`IntegrationData.integral_finsetSum`) and local (`IntegrationData.integral_eq_chartIntegral`).
* **Existence** (`exists_integrationData`): on a Hausdorff σ-compact `M`, for every compact `s`
  (Mathlib's smooth partitions of unity, `SmoothPartitionOfUnity.exists_isSubordinate`).
* **The integral** `ManifoldForm.integral o ω = ∫_M ω` of a continuous compactly supported
  `n`-form, with `integral_eq_integrationData` (it is the integral for every integration datum),
  `integral_eq_chartIntegral` (a form supported in a signed chart), linearity
  (`integral_add`, `integral_finsetSum`), `integral_neg_orientation` (`∫` for `-o` is `-∫`), and
  `integral_eq_chartIntegral_of_isOrientedAtlas` (an oriented atlas: its charts are positive).
-/

open Set Filter Topology Manifold Module MeasureTheory

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- Mathlib's model with corners `[0,∞)ⁿ ⊆ ℝⁿ`. -/
local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

/-! ### Signs of charts -/

section Signs

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*}

/-- The orientation `ρ` (`b = true`) or `-ρ` (`b = false`). -/
def signedOr (b : Bool) (ρ : Orientation ℝ E ι) : Orientation ℝ E ι := cond b ρ (-ρ)

/-- The sign `1` (`b = true`) or `-1` (`b = false`). -/
def orSign (b : Bool) : ℝ := cond b 1 (-1)

@[simp] theorem signedOr_true (ρ : Orientation ℝ E ι) : signedOr true ρ = ρ := rfl

@[simp] theorem signedOr_false (ρ : Orientation ℝ E ι) : signedOr false ρ = -ρ := rfl

@[simp] theorem orSign_true : orSign true = 1 := rfl

@[simp] theorem orSign_false : orSign false = -1 := rfl

theorem orSign_mul_self (b : Bool) : orSign b * orSign b = 1 := by cases b <;> simp

@[simp] theorem signedOr_not (b : Bool) (ρ : Orientation ℝ E ι) :
    signedOr (!b) ρ = -signedOr b ρ := by
  cases b
  · exact (neg_neg ρ).symm
  · rfl

@[simp] theorem orSign_not (b : Bool) : orSign (!b) = -orSign b := by cases b <;> simp

end Signs

/-- The standard orientation of `ℝⁿ`: the one of the standard basis. -/
def stdOrientation (n : ℕ) : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n) :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.orientation

section ChartSign

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {k : ℕ}

/-- **The sign of a chart change between signed charts**: if a tangent orientation reads as
`signedOr b ρ` in `e` and `signedOr b' ρ` in `e'` at `x`, then `det D(e' ∘ e⁻¹)(x)` has the sign
`orSign b · orSign b'`. -/
theorem orSign_mul_det_chartChangeDeriv_pos {o : TangentOrientation I M k}
    {ρ : Orientation ℝ E (Fin k)} {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) (he' : e' ∈ IsManifold.maximalAtlas I ∞ M) {x : M}
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) {b b' : Bool}
    (h : orientationIn e x (o x) = signedOr b ρ) (h' : orientationIn e' x (o x) = signedOr b' ρ) :
    0 < orSign b * orSign b' * (chartChangeDeriv I e e' x).det := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hc := orientationIn_chartChange hn he he' hx hx' (o x)
  rw [h, h'] at hc
  have hne := det_chartChangeDeriv_ne_zero hn he he' hx hx'
  have key : ∀ {A : E →L[ℝ] E}, A.det ≠ 0 → signMap A ρ = -ρ → A.det < 0 := fun hA h2 =>
    lt_of_le_of_ne (not_lt.1 fun hpos => Module.Ray.ne_neg_self ρ
      (((signMap_eq_self_iff ρ).2 hpos).symm.trans h2)) hA
  cases b <;> cases b' <;> simp only [signedOr_true, signedOr_false, orSign_true,
    orSign_false, signMap_neg] at hc ⊢
  · have := (signMap_eq_self_iff ρ).1 (neg_injective hc.symm); linarith
  · have h2 := congrArg Neg.neg hc
    rw [neg_neg (signMap (chartChangeDeriv I e e' x) ρ)] at h2
    have := key hne h2.symm; linarith
  · have := key hne hc.symm; linarith
  · have := (signMap_eq_self_iff ρ).1 hc.symm; linarith

/-- The sign of `det D(e' ∘ e⁻¹)(x)` between signed charts, as a `SignType` cast. -/
theorem sign_det_chartChangeDeriv {o : TangentOrientation I M k}
    {ρ : Orientation ℝ E (Fin k)} {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) (he' : e' ∈ IsManifold.maximalAtlas I ∞ M) {x : M}
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) {b b' : Bool}
    (h : orientationIn e x (o x) = signedOr b ρ) (h' : orientationIn e' x (o x) = signedOr b' ρ) :
    (SignType.sign (chartChangeDeriv I e e' x).det : ℝ) = orSign b * orSign b' := by
  have := orSign_mul_det_chartChangeDeriv_pos he he' hx hx' h h'
  cases b <;> cases b' <;> simp only [orSign_true, orSign_false] at this ⊢
  · rw [sign_pos (by linarith)]; norm_num
  · rw [sign_neg (by linarith)]; norm_num
  · rw [sign_neg (by linarith)]; norm_num
  · rw [sign_pos (by linarith)]; norm_num

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- The opposite orientation reads as the opposite in every chart. -/
theorem orientationIn_neg (e : OpenPartialHomeomorph M H) (x : M)
    (o : Orientation ℝ (TangentSpace I x) (Fin k)) :
    orientationIn e x (-o) = -orientationIn e x o :=
  signMap_neg _ _

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- **The opposite of a continuous tangent orientation is continuous.** -/
theorem TangentOrientation.IsContinuous.neg {o : TangentOrientation I M k} {r : WithTop ℕ∞}
    (ho : o.IsContinuous I r) : TangentOrientation.IsContinuous I r (-o) := fun e he x hx => by
  filter_upwards [ho e he x hx] with y hy
  simp only [Pi.neg_apply, orientationIn_neg, hy]

end ChartSign

/-! ### Chart integrals -/

namespace ManifoldForm

section ChartIntegral

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant n) M]

/-- **The integral of an `n`-form in a chart**: `∫_{e(U)} (e⁻¹)^*ω`, the integral of the
expression of `ω` in `e` over the chart target, for the standard orientation of `ℝⁿ`. -/
def chartIntegral (e : OpenPartialHomeomorph M (EuclideanQuadrant n))
    (ω : ManifoldForm (𝓠 n) M n) : ℝ :=
  topFormIntegral (e.extend (𝓠 n)).target (chartForm (𝓠 n) e ω)

omit [ChartedSpace (EuclideanQuadrant n) M] in
theorem measurableSet_extend_target (e : OpenPartialHomeomorph M (EuclideanQuadrant n)) :
    MeasurableSet (e.extend (𝓠 n)).target := by
  rw [e.extend_target]
  exact (e.open_target.preimage (𝓠 n).continuous_symm).measurableSet.inter
    (𝓠 n).isClosed_range.measurableSet

omit [ChartedSpace (EuclideanQuadrant n) M] in
/-- The source of a chart change is the relatively open set `I(e(U ∩ U'))` of `range I`. -/
theorem extendCoordChange_source_eq (e e' : OpenPartialHomeomorph M (EuclideanQuadrant n)) :
    ((𝓠 n).extendCoordChange e e').source =
      (𝓠 n).symm ⁻¹' (e.target ∩ e.symm ⁻¹' e'.source) ∩ range (𝓠 n) := by
  ext y
  simp only [PartialEquiv.trans_source,
    PartialEquiv.symm_source, e.extend_target, mem_inter_iff, mem_preimage,
    OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply, e'.extend_source]
  tauto

omit [ChartedSpace (EuclideanQuadrant n) M] in
theorem measurableSet_extendCoordChange_source
    (e e' : OpenPartialHomeomorph M (EuclideanQuadrant n)) :
    MeasurableSet ((𝓠 n).extendCoordChange e e').source := by
  rw [extendCoordChange_source_eq]
  exact (((e.isOpen_inter_preimage_symm e'.open_source).preimage
    (𝓠 n).continuous_symm).measurableSet).inter (𝓠 n).isClosed_range.measurableSet

/-- A form continuous in a chart and vanishing outside a compact subset `K` of the chart source
has an integrable expression in that chart. -/
theorem integrableOn_chartForm {e : OpenPartialHomeomorph M (EuclideanQuadrant n)}
    {ω : ManifoldForm (𝓠 n) M n}
    (hω : ContinuousOn (chartForm (𝓠 n) e ω) (e.extend (𝓠 n)).target) {K : Set M}
    (hK : IsCompact K) (hKe : K ⊆ e.source) (hω0 : ∀ x ∉ K, ω x = 0) :
    IntegrableOn (fun y => chartForm (𝓠 n) e ω y (stdFrame n)) (e.extend (𝓠 n)).target := by
  have hCK : IsCompact (e.extend (𝓠 n) '' K) :=
    hK.image_of_continuousOn (e.continuousOn_extend.mono (by rwa [e.extend_source]))
  have hCt : e.extend (𝓠 n) '' K ⊆ (e.extend (𝓠 n)).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (e.extend (𝓠 n)).map_source (by rw [e.extend_source]; exact hKe hx)
  have hc : ContinuousOn (fun y => chartForm (𝓠 n) e ω y (stdFrame n))
      (e.extend (𝓠 n)).target :=
    (ContinuousAlternatingMap.apply ℝ _ ℝ (stdFrame n)).continuous.comp_continuousOn hω
  refine IntegrableOn.of_forall_sdiff_eq_zero ((hc.mono hCt).integrableOn_compact hCK)
    (measurableSet_extend_target e) fun y hy => ?_
  have : (e.extend (𝓠 n)).symm y ∉ K := fun h => hy.2
    ⟨_, h, (e.extend (𝓠 n)).right_inv hy.1⟩
  rw [chartForm_eq_zero_of_notMem hω0 e this]
  rfl

/-- **Linearity of the chart integral** for forms continuous in the chart and vanishing outside
compact subsets of the chart source. -/
theorem chartIntegral_finsetSum {ι : Type*} (u : Finset ι)
    {e : OpenPartialHomeomorph M (EuclideanQuadrant n)} {ω : ι → ManifoldForm (𝓠 n) M n}
    (hω : ∀ j ∈ u, ContinuousOn (chartForm (𝓠 n) e (ω j)) (e.extend (𝓠 n)).target)
    {K : ι → Set M} (hK : ∀ j ∈ u, IsCompact (K j)) (hKe : ∀ j ∈ u, K j ⊆ e.source)
    (hω0 : ∀ j ∈ u, ∀ x ∉ K j, ω j x = 0) :
    chartIntegral e (∑ j ∈ u, ω j) = ∑ j ∈ u, chartIntegral e (ω j) := by
  rw [chartIntegral, chartForm_finsetSum]
  have : chartForm (𝓠 n) e (∑ j ∈ u, ω j) = fun y => ∑ j ∈ u, chartForm (𝓠 n) e (ω j) y := by
    rw [chartForm_finsetSum]; funext y; simp
  rw [← chartForm_finsetSum, this]
  exact topFormIntegral_finsetSum u _ fun j hj =>
    integrableOn_chartForm (hω j hj) (hK j hj) (hKe j hj) (hω0 j hj)

variable [IsManifold (𝓠 n) ∞ M]

/-- **The change of charts for the chart integral**: for an `n`-form `ω` vanishing outside a set
`K` inside the overlap of two charts `e`, `e'` of the maximal atlas,
`∫_{e'} ω = ∫_{e(U)} sign(det D(e' ∘ e⁻¹)) · (e⁻¹)^*ω` (the change of variables formula
`topFormIntegral_image` for the chart change, `chartForm_eq_formPullback`). -/
theorem chartIntegral_eq_integral_sign {e e' : OpenPartialHomeomorph M (EuclideanQuadrant n)}
    (he : e ∈ IsManifold.maximalAtlas (𝓠 n) ∞ M) (he' : e' ∈ IsManifold.maximalAtlas (𝓠 n) ∞ M)
    {ω : ManifoldForm (𝓠 n) M n} {K : Set M} (hKe : K ⊆ e.source ∩ e'.source)
    (hω0 : ∀ x ∉ K, ω x = 0) :
    chartIntegral e' ω = ∫ y in (e.extend (𝓠 n)).target,
      (SignType.sign (chartChangeDeriv (𝓠 n) e e' ((e.extend (𝓠 n)).symm y)).det : ℝ) *
        chartForm (𝓠 n) e ω y (stdFrame n) := by
  set f := (𝓠 n).extendCoordChange e e' with hf
  set s := f.source with hs_def
  set f' : EuclideanSpace ℝ (Fin n) → _ :=
    fun y => chartChangeDeriv (𝓠 n) e e' ((e.extend (𝓠 n)).symm y) with hf'
  have hs : MeasurableSet s := measurableSet_extendCoordChange_source e e'
  have hs_eq : s = e.extend (𝓠 n) '' (e.source ∩ e'.source) :=
    (OpenPartialHomeomorph.extend_image_source_inter e e').symm
  -- the image of the overlap in `e'`
  have himage : f '' s = e'.extend (𝓠 n) '' (e.source ∩ e'.source) := by
    rw [f.image_source_eq_target, inter_comm, OpenPartialHomeomorph.extend_image_source_inter]
    rfl
  have hsub' : f '' s ⊆ (e'.extend (𝓠 n)).target := by
    rw [himage]; rintro _ ⟨x, hx, rfl⟩
    exact (e'.extend (𝓠 n)).map_source (by rw [e'.extend_source]; exact hx.2)
  have hsub : s ⊆ (e.extend (𝓠 n)).target := by
    rw [hs_eq]; rintro _ ⟨x, hx, rfl⟩
    exact (e.extend (𝓠 n)).map_source (by rw [e.extend_source]; exact hx.1)
  have hsI : s ⊆ range (𝓠 n) := hsub.trans (e.extend_target_subset_range (I := 𝓠 n))
  have hpull : ∀ y ∈ s, formPullback f f' (chartForm (𝓠 n) e' ω) y = chartForm (𝓠 n) e ω y := by
    intro y hy
    rw [hs_eq] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [chartForm_eq_formPullback he he' ω hx.1 hx.2]
    ext v
    simp only [formPullback_apply, hf', e.extend_left_inv hx.1]
    rfl
  have h0' : ∀ y ∈ (e'.extend (𝓠 n)).target \ f '' s, chartForm (𝓠 n) e' ω y = 0 := by
    intro y hy
    have hy' : (e'.extend (𝓠 n)).symm y ∉ K := fun hK => hy.2 (by
      rw [himage]
      exact ⟨_, hKe hK, (e'.extend (𝓠 n)).right_inv hy.1⟩)
    exact chartForm_eq_zero_of_notMem hω0 e' hy'
  have hderiv : ∀ y ∈ s, HasFDerivWithinAt f (f' y) s y := by
    intro y hy
    have hy' := hy
    rw [hs_eq] at hy'
    obtain ⟨x, hx, rfl⟩ := hy'
    simp only [hf', e.extend_left_inv hx.1]
    exact (hasFDerivWithinAt_chartChangeDeriv (by simp) he he' hx.1 hx.2).mono hsI
  have h0 : ∀ y ∈ (e.extend (𝓠 n)).target \ s,
      (SignType.sign (chartChangeDeriv (𝓠 n) e e' ((e.extend (𝓠 n)).symm y)).det : ℝ) *
        chartForm (𝓠 n) e ω y (stdFrame n) = 0 := by
    intro y hy
    have hy' : (e.extend (𝓠 n)).symm y ∉ K := fun hK => hy.2 (by
      rw [hs_eq]
      exact ⟨_, hKe hK, (e.extend (𝓠 n)).right_inv hy.1⟩)
    rw [chartForm_eq_zero_of_notMem hω0 e hy']
    simp
  -- restrict both integrals to the overlap
  rw [chartIntegral, topFormIntegral_eq_of_subset (measurableSet_extend_target e') hsub' h0',
    topFormIntegral_image hs hderiv f.injOn,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_extend_target e) hsub h0]
  refine setIntegral_congr_fun hs fun y hy => ?_
  rw [hpull y hy]

/-- **Change of charts with positive determinant**: the chart integrals agree. -/
theorem chartIntegral_eq_of_det_pos {e e' : OpenPartialHomeomorph M (EuclideanQuadrant n)}
    (he : e ∈ IsManifold.maximalAtlas (𝓠 n) ∞ M) (he' : e' ∈ IsManifold.maximalAtlas (𝓠 n) ∞ M)
    {ω : ManifoldForm (𝓠 n) M n} {K : Set M} (hKe : K ⊆ e.source ∩ e'.source)
    (hω0 : ∀ x ∉ K, ω x = 0) (hdet : ∀ x ∈ K, 0 < (chartChangeDeriv (𝓠 n) e e' x).det) :
    chartIntegral e' ω = chartIntegral e ω := by
  rw [chartIntegral_eq_integral_sign he he' hKe hω0, chartIntegral, topFormIntegral]
  refine setIntegral_congr_fun (measurableSet_extend_target e) fun y _ => ?_
  by_cases hK : (e.extend (𝓠 n)).symm y ∈ K
  · rw [sign_pos (hdet _ hK)]; simp
  · rw [chartForm_eq_zero_of_notMem hω0 e hK]; simp

/-- **Change of charts between signed charts**: if `o` reads as `signedOr b (stdOrientation n)`
in `e` and as `signedOr b' (stdOrientation n)` in `e'` at the points of `K`, then
`orSign b' · ∫_{e'} ω = orSign b · ∫_e ω`. -/
theorem orSign_mul_chartIntegral_eq {o : TangentOrientation (𝓠 n) M n}
    {e e' : OpenPartialHomeomorph M (EuclideanQuadrant n)}
    (he : e ∈ IsManifold.maximalAtlas (𝓠 n) ∞ M) (he' : e' ∈ IsManifold.maximalAtlas (𝓠 n) ∞ M)
    {ω : ManifoldForm (𝓠 n) M n} {K : Set M} (hKe : K ⊆ e.source ∩ e'.source)
    (hω0 : ∀ x ∉ K, ω x = 0) {b b' : Bool}
    (hb : ∀ x ∈ K, orientationIn e x (o x) = signedOr b (stdOrientation n))
    (hb' : ∀ x ∈ K, orientationIn e' x (o x) = signedOr b' (stdOrientation n)) :
    orSign b' * chartIntegral e' ω = orSign b * chartIntegral e ω := by
  rw [chartIntegral_eq_integral_sign he he' hKe hω0, chartIntegral, topFormIntegral,
    ← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_extend_target e) fun y hy => ?_
  by_cases hK : (e.extend (𝓠 n)).symm y ∈ K
  · rw [sign_det_chartChangeDeriv he he' (hKe hK).1 (hKe hK).2 (hb _ hK) (hb' _ hK)]
    have := orSign_mul_self b'
    calc orSign b' * (orSign b * orSign b' * chartForm (𝓠 n) e ω y (stdFrame n))
        = (orSign b' * orSign b') * (orSign b * chartForm (𝓠 n) e ω y (stdFrame n)) := by ring
      _ = _ := by rw [this, one_mul]
  · rw [chartForm_eq_zero_of_notMem hω0 e hK]; simp

end ChartIntegral

section SmulFun

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {k : ℕ}

theorem smulFun_finsetSum {κ : Type*} (u : Finset κ) (f : M → ℝ) (ω : κ → ManifoldForm I M k) :
    smulFun f (∑ j ∈ u, ω j) = ∑ j ∈ u, smulFun f (ω j) := by
  funext x
  simp only [smulFun_apply, Finset.sum_apply, Finset.smul_sum]

/-- `f ω` vanishes outside `tsupport f ∩ K` if `ω` vanishes outside `K`. -/
theorem smulFun_eq_zero_of_notMem {f : M → ℝ} {ω : ManifoldForm I M k} {K : Set M}
    (hω0 : ∀ x ∉ K, ω x = 0) {x : M} (hx : x ∉ _root_.tsupport f ∩ K) : smulFun f ω x = 0 := by
  rw [smulFun_apply]
  by_cases hf : x ∈ _root_.tsupport f
  · rw [hω0 x fun hK => hx ⟨hf, hK⟩, smul_zero]
  · rw [image_eq_zero_of_notMem_tsupport hf, zero_smul]

/-- If `∑ fⱼ = 1` on `s` and `ω` vanishes outside `K ⊆ s`, then `∑ fⱼ ω = ω`. -/
theorem finsetSum_smulFun_eq_self {κ : Type*} (u : Finset κ) {f : κ → M → ℝ} {s : Set M}
    (hf : ∀ x ∈ s, ∑ j ∈ u, f j x = 1) {ω : ManifoldForm I M k} {K : Set M} (hKs : K ⊆ s)
    (hω0 : ∀ x ∉ K, ω x = 0) : ∑ j ∈ u, smulFun (f j) ω = ω := by
  rw [finsetSum_smulFun]
  funext x
  rw [smulFun_apply]
  by_cases hx : x ∈ K
  · rw [hf x (hKs hx), one_smul]
  · rw [hω0 x hx, smul_zero]

theorem tsupport_finsetSum_subset {κ : Type*} (u : Finset κ) (ω : κ → ManifoldForm I M k) :
    tsupport (∑ j ∈ u, ω j) ⊆ ⋃ j ∈ u, tsupport (ω j) := by
  refine closure_minimal (fun x hx => ?_) (u.finite_toSet.isClosed_biUnion fun _ _ =>
    isClosed_closure)
  by_contra h
  simp only [mem_iUnion, not_exists] at h
  refine hx ?_
  rw [Finset.sum_apply]
  exact Finset.sum_eq_zero fun j hj => eq_zero_of_notMem_tsupport (h j hj)

end SmulFun

end ManifoldForm

/-! ### Integration data: smooth partitions of unity subordinate to signed charts -/

section IntegrationData

open ManifoldForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant n) M]
  [IsManifold (𝓠 n) ∞ M]

variable (M) in
/-- **Integration data on a set `s`** for a tangent orientation `o` of `M`: a finite family of
charts `chartAt H cⱼ` with regions `Vⱼ ⊆` their sources on which `o` reads as
`signedOr bⱼ (stdOrientation n)` (the chart is positive, `bⱼ = true`, or negative there), and
smooth functions `ρⱼ` with `tsupport ρⱼ ⊆ Vⱼ` and `∑ⱼ ρⱼ = 1` on `s`: a smooth partition of
unity on `s` subordinate to signed charts.  They exist for every compact `s`
(`exists_integrationData`). -/
structure IntegrationData (o : TangentOrientation (𝓠 n) M n) (s : Set M) (ι : Type*)
    [Fintype ι] where
  /-- The centres of the charts `chartAt H (center j)`. -/
  center : ι → M
  /-- The regions in which the charts are signed. -/
  region : ι → Set M
  region_subset : ∀ j, region j ⊆ (chartAt (EuclideanQuadrant n) (center j)).source
  /-- The signs of the charts on their regions. -/
  sign : ι → Bool
  orientationIn_eq : ∀ j, ∀ x ∈ region j,
    orientationIn (chartAt (EuclideanQuadrant n) (center j)) x (o x) =
      signedOr (sign j) (stdOrientation n)
  /-- The partition of unity. -/
  ρ : ι → M → ℝ
  contMDiff_ρ : ∀ j, ContMDiff (𝓠 n) 𝓘(ℝ) ∞ (ρ j)
  tsupport_subset : ∀ j, tsupport (ρ j) ⊆ region j
  sum_eq_one : ∀ x ∈ s, ∑ j, ρ j x = 1

namespace IntegrationData

variable {o : TangentOrientation (𝓠 n) M n} {s : Set M} {ι : Type*} [Fintype ι]
  (D : IntegrationData M o s ι)

/-- The chart `chartAt H (center j)` of the datum. -/
abbrev chart (j : ι) : OpenPartialHomeomorph M (EuclideanQuadrant n) :=
  chartAt (EuclideanQuadrant n) (D.center j)

/-- **The integral of an `n`-form with respect to integration data**:
`∑ⱼ (±ⱼ) ∫_{e_j} (e_j⁻¹)^*(ρⱼ ω)`, the sign `±ⱼ = orSign bⱼ` being the sign of the chart `e_j`
for `o`. -/
def integral (ω : ManifoldForm (𝓠 n) M n) : ℝ :=
  ∑ j, orSign (D.sign j) * chartIntegral (D.chart j) (smulFun (D.ρ j) ω)

include D in
theorem contMDiffForm_smulFun {r : WithTop ℕ∞} (hr : r ≤ ∞) (j : ι) {k : ℕ}
    {ω : ManifoldForm (𝓠 n) M k} (hω : ContMDiffForm (𝓠 n) r ω) :
    ContMDiffForm (𝓠 n) r (smulFun (D.ρ j) ω) :=
  ContMDiffForm.smulFun hr ((D.contMDiff_ρ j).of_le hr) hω

theorem continuousOn_chartForm_smulFun {ω : ManifoldForm (𝓠 n) M n}
    (hω : ContMDiffForm (𝓠 n) 0 ω) (j : ι) (x : M) :
    ContinuousOn (chartForm (𝓠 n) (chartAt (EuclideanQuadrant n) x) (smulFun (D.ρ j) ω))
      ((chartAt (EuclideanQuadrant n) x).extend (𝓠 n)).target :=
  (D.contMDiffForm_smulFun (by simp) j hω x).continuousOn

/-- **Linearity** of the integral with respect to integration data, for continuous forms
vanishing outside compact sets. -/
theorem integral_finsetSum {κ : Type*} (u : Finset κ) {ω : κ → ManifoldForm (𝓠 n) M n}
    (hω : ∀ i ∈ u, ContMDiffForm (𝓠 n) 0 (ω i)) {K : κ → Set M} (hK : ∀ i ∈ u, IsCompact (K i))
    (hω0 : ∀ i ∈ u, ∀ x ∉ K i, ω i x = 0) :
    D.integral (∑ i ∈ u, ω i) = ∑ i ∈ u, D.integral (ω i) := by
  simp only [integral, smulFun_finsetSum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  exact chartIntegral_finsetSum u (fun i hi => D.continuousOn_chartForm_smulFun (hω i hi) j _)
    (fun i hi => (hK i hi).inter_left (isClosed_tsupport _))
    (fun i hi => fun x hx => D.region_subset j (D.tsupport_subset j hx.1))
    (fun i hi => fun x hx => smulFun_eq_zero_of_notMem (hω0 i hi) hx)

/-- **Localization**: for a continuous form vanishing outside a compact `K ⊆ s` lying in a region
`V` of a chart `chartAt H x₀` on which `o` reads as `signedOr b (stdOrientation n)`, the integral
is `orSign b · ∫_{x₀} ω`. -/
theorem integral_eq_chartIntegral {ω : ManifoldForm (𝓠 n) M n} (hω : ContMDiffForm (𝓠 n) 0 ω)
    {x₀ : M} {V : Set M} (hV : V ⊆ (chartAt (EuclideanQuadrant n) x₀).source) {b : Bool}
    (hb : ∀ x ∈ V, orientationIn (chartAt (EuclideanQuadrant n) x₀) x (o x) =
      signedOr b (stdOrientation n))
    {K : Set M} (hK : IsCompact K) (hKV : K ⊆ V) (hKs : K ⊆ s) (hω0 : ∀ x ∉ K, ω x = 0) :
    D.integral ω = orSign b * chartIntegral (chartAt (EuclideanQuadrant n) x₀) ω := by
  have step : ∀ j, orSign (D.sign j) * chartIntegral (D.chart j) (smulFun (D.ρ j) ω) =
      orSign b * chartIntegral (chartAt (EuclideanQuadrant n) x₀) (smulFun (D.ρ j) ω) :=
    fun j => orSign_mul_chartIntegral_eq (IsManifold.chart_mem_maximalAtlas x₀)
      (IsManifold.chart_mem_maximalAtlas (D.center j)) (K := _root_.tsupport (D.ρ j) ∩ K)
      (fun x hx => ⟨hV (hKV hx.2), D.region_subset j (D.tsupport_subset j hx.1)⟩)
      (fun x hx => smulFun_eq_zero_of_notMem hω0 hx) (fun x hx => hb x (hKV hx.2))
      (fun x hx => D.orientationIn_eq j x (D.tsupport_subset j hx.1))
  rw [integral, Finset.sum_congr rfl fun j _ => step j, ← Finset.mul_sum,
    ← chartIntegral_finsetSum Finset.univ (fun j _ => D.continuousOn_chartForm_smulFun hω j x₀)
      (fun j _ => hK.inter_left (isClosed_tsupport (D.ρ j)))
      (fun j _ => fun x hx => hV (hKV hx.2))
      (fun j _ => fun x hx => smulFun_eq_zero_of_notMem hω0 hx),
    finsetSum_smulFun_eq_self Finset.univ D.sum_eq_one hKs hω0]

/-- **Independence of the integration data**: two integration data (for the same orientation)
give the same integral of a continuous `n`-form vanishing outside a compact set contained in both
of their domains. -/
theorem integral_eq {s' : Set M} {ι' : Type*} [Fintype ι'] (D' : IntegrationData M o s' ι')
    {ω : ManifoldForm (𝓠 n) M n} (hω : ContMDiffForm (𝓠 n) 0 ω) {K : Set M} (hK : IsCompact K)
    (hKs : K ⊆ s) (hKs' : K ⊆ s') (hω0 : ∀ x ∉ K, ω x = 0) :
    D.integral ω = D'.integral ω := by
  have hloc : ∀ k, D.integral (smulFun (D'.ρ k) ω) =
      orSign (D'.sign k) * chartIntegral (D'.chart k) (smulFun (D'.ρ k) ω) := fun k =>
    D.integral_eq_chartIntegral (D'.contMDiffForm_smulFun (by simp) k hω) (D'.region_subset k)
      (D'.orientationIn_eq k) (hK.inter_left (isClosed_tsupport (D'.ρ k)))
      (fun x hx => D'.tsupport_subset k hx.1) (fun x hx => hKs hx.2)
      (fun x hx => smulFun_eq_zero_of_notMem hω0 hx)
  conv_rhs => rw [IntegrationData.integral]
  rw [← Finset.sum_congr rfl fun k _ => hloc k,
    ← D.integral_finsetSum Finset.univ (fun k _ => D'.contMDiffForm_smulFun (by simp) k hω)
      (fun k _ => hK.inter_left (isClosed_tsupport (D'.ρ k)))
      (fun k _ => fun x hx => smulFun_eq_zero_of_notMem hω0 hx),
    finsetSum_smulFun_eq_self Finset.univ D'.sum_eq_one hKs' hω0]

/-- **Integration data for the opposite orientation**: the same charts with the opposite signs. -/
def neg : IntegrationData M (-o) s ι :=
  { D with
    sign := fun j => !D.sign j
    orientationIn_eq := fun j x hx => by
      rw [Pi.neg_apply, orientationIn_neg, D.orientationIn_eq j x hx, signedOr_not] }

omit [IsManifold (𝓠 n) ∞ M] in
/-- **Reversing the orientation changes the sign of the integral.** -/
theorem integral_neg (ω : ManifoldForm (𝓠 n) M n) : D.neg.integral ω = -D.integral ω := by
  simp only [integral, neg, orSign_not, neg_mul, Finset.sum_neg_distrib]

/-- Additivity of the integral with respect to integration data. -/
theorem integral_add {ω₁ ω₂ : ManifoldForm (𝓠 n) M n} (h₁ : ContMDiffForm (𝓠 n) 0 ω₁)
    (h₂ : ContMDiffForm (𝓠 n) 0 ω₂) {K₁ K₂ : Set M} (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (h₁0 : ∀ x ∉ K₁, ω₁ x = 0) (h₂0 : ∀ x ∉ K₂, ω₂ x = 0) :
    D.integral (ω₁ + ω₂) = D.integral ω₁ + D.integral ω₂ := by
  have := D.integral_finsetSum Finset.univ (ω := fun b : Bool => cond b ω₁ ω₂)
    (K := fun b => cond b K₁ K₂) (fun b _ => by cases b <;> assumption)
    (fun b _ => by cases b <;> assumption) (fun b _ => by cases b <;> assumption)
  simpa [Fintype.sum_bool] using this

end IntegrationData

/-- **Existence of integration data** on every compact set `s`, for a continuous tangent
orientation of a Hausdorff σ-compact manifold: around every point `x` the chart `chartAt H x` is
signed on the open set `V x` of the points where `o` reads in it as at `x` (`o` is continuous);
Mathlib's smooth partition of unity subordinate to `V` has only finitely many members meeting
`s`. -/
theorem exists_integrationData [T2Space M] [SigmaCompactSpace M]
    {o : TangentOrientation (𝓠 n) M n} (ho : o.IsContinuous (𝓠 n) ∞) {s : Set M}
    (hs : IsCompact s) : ∃ T : Finset M, Nonempty (IntegrationData M o s {x // x ∈ T}) := by
  classical
  set H := EuclideanQuadrant n
  set r : M → Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n) :=
    fun x => orientationIn (chartAt H x) x (o x) with hr
  set V : M → Set M := fun x => {y | y ∈ (chartAt H x).source ∧
    orientationIn (chartAt H x) y (o y) = r x} with hV
  have hVo : ∀ x, IsOpen (V x) := fun x => by
    refine isOpen_iff_mem_nhds.2 fun y hy => ?_
    filter_upwards [(chartAt H x).open_source.mem_nhds hy.1,
      ho _ (IsManifold.chart_mem_maximalAtlas x) y hy.1] with z hz hz'
    exact ⟨hz, hz'.trans hy.2⟩
  have hxV : ∀ x, x ∈ V x := fun x => ⟨mem_chart_source H x, rfl⟩
  have hsign : ∀ x, r x = signedOr (decide (r x = stdOrientation n)) (stdOrientation n) := by
    intro x
    by_cases h : r x = stdOrientation n
    · simp [h]
    · simp only [h, decide_false, signedOr_false]
      exact ((r x).eq_or_eq_neg (stdOrientation n) (by simp)).resolve_left h
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓠 n) isClosed_univ V hVo
    fun x _ => mem_iUnion.2 ⟨x, hxV x⟩
  have hT := f.locallyFinite.finite_nonempty_inter_compact hs
  refine ⟨hT.toFinset, ⟨{
    center := fun j => j.1
    region := fun j => V j.1
    region_subset := fun j _ hy => hy.1
    sign := fun j => decide (r j.1 = stdOrientation n)
    orientationIn_eq := fun j y hy => hy.2.trans (hsign j.1)
    ρ := fun j => f j.1
    contMDiff_ρ := fun j => (f j.1).contMDiff
    tsupport_subset := fun j => hf j.1
    sum_eq_one := fun x hx => ?_ }⟩⟩
  rw [Finset.sum_coe_sort hT.toFinset (fun i => f i x), ← f.sum_eq_one (mem_univ x)]
  refine (finsum_eq_sum_of_support_subset _ fun i hi => ?_).symm
  rw [Set.Finite.coe_toFinset]
  exact ⟨x, hi, hx⟩

end IntegrationData

/-! ### The integral over `M` -/

namespace ManifoldForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant n) M]
  [IsManifold (𝓠 n) ∞ M]

open Classical in
/-- **The integral `∫_M ω` of an `n`-form** over the `n`-dimensional manifold with corners `M`,
oriented by the tangent orientation `o`: the integral with respect to a chosen integration datum on
the support of `ω` (`0` if there is none).  For a continuous compactly supported form on a
Hausdorff σ-compact `M` with a continuous orientation it is the integral with respect to every
integration datum (`integral_eq_integrationData`). -/
def integral (o : TangentOrientation (𝓠 n) M n) (ω : ManifoldForm (𝓠 n) M n) : ℝ :=
  if h : ∃ T : Finset M, Nonempty (IntegrationData M o (tsupport ω) {x // x ∈ T}) then
    (Classical.choice h.choose_spec).integral ω
  else 0

variable [T2Space M] [SigmaCompactSpace M] {o : TangentOrientation (𝓠 n) M n}

/-- **`∫_M ω` is the integral with respect to any integration datum** whose domain contains the
support of `ω`, for a continuous form with compact support and a continuous orientation. -/
theorem integral_eq_integrationData (ho : o.IsContinuous (𝓠 n) ∞) {ω : ManifoldForm (𝓠 n) M n}
    (hω : ContMDiffForm (𝓠 n) 0 ω) (hc : IsCompact (tsupport ω)) {s : Set M} {ι : Type*}
    [Fintype ι] (D : IntegrationData M o s ι) (hs : tsupport ω ⊆ s) :
    integral o ω = D.integral ω := by
  have h := exists_integrationData ho hc
  rw [integral, dif_pos h]
  exact (Classical.choice h.choose_spec).integral_eq D hω hc subset_rfl hs
    fun x hx => eq_zero_of_notMem_tsupport hx

/-- **A form supported in a signed chart**: if `ω` (continuous) vanishes outside a compact set
`K` lying in a region `V` of the chart at `x₀` on which `o` reads as
`signedOr b (stdOrientation n)`, then `∫_M ω = orSign b · ∫_{x₀} ω`. -/
theorem integral_eq_chartIntegral (ho : o.IsContinuous (𝓠 n) ∞) {ω : ManifoldForm (𝓠 n) M n}
    (hω : ContMDiffForm (𝓠 n) 0 ω) {x₀ : M} {V : Set M}
    (hV : V ⊆ (chartAt (EuclideanQuadrant n) x₀).source) {b : Bool}
    (hb : ∀ x ∈ V, orientationIn (chartAt (EuclideanQuadrant n) x₀) x (o x) =
      signedOr b (stdOrientation n))
    {K : Set M} (hK : IsCompact K) (hKV : K ⊆ V) (hω0 : ∀ x ∉ K, ω x = 0) :
    integral o ω = orSign b * chartIntegral (chartAt (EuclideanQuadrant n) x₀) ω := by
  have hsK : tsupport ω ⊆ K := closure_minimal (fun x hx => by_contra fun h => hx (hω0 x h))
    hK.isClosed
  obtain ⟨T, ⟨D⟩⟩ := exists_integrationData ho hK
  rw [integral_eq_integrationData ho hω (hK.of_isClosed_subset isClosed_closure hsK) D hsK]
  exact D.integral_eq_chartIntegral hω hV hb hK hKV subset_rfl hω0

/-- **Linearity of `∫_M`** for continuous compactly supported forms. -/
theorem integral_finsetSum (ho : o.IsContinuous (𝓠 n) ∞) {κ : Type*} (u : Finset κ)
    {ω : κ → ManifoldForm (𝓠 n) M n} (hω : ∀ i ∈ u, ContMDiffForm (𝓠 n) 0 (ω i))
    (hc : ∀ i ∈ u, IsCompact (tsupport (ω i))) :
    integral o (∑ i ∈ u, ω i) = ∑ i ∈ u, integral o (ω i) := by
  have hK : IsCompact (⋃ i ∈ u, tsupport (ω i)) := u.finite_toSet.isCompact_biUnion hc
  obtain ⟨T, ⟨D⟩⟩ := exists_integrationData ho hK
  have hsub := tsupport_finsetSum_subset u ω
  rw [integral_eq_integrationData ho (ContMDiffForm.finsetSum u hω)
    (hK.of_isClosed_subset isClosed_closure hsub) D hsub,
    D.integral_finsetSum u hω hc fun i _ x hx => eq_zero_of_notMem_tsupport hx]
  exact Finset.sum_congr rfl fun i hi => (integral_eq_integrationData ho (hω i hi) (hc i hi) D
    (subset_biUnion_of_mem (u := fun i => tsupport (ω i)) hi)).symm

/-- **Reversing the orientation changes the sign of `∫_M ω`.** -/
theorem integral_neg_orientation (ho : o.IsContinuous (𝓠 n) ∞) {ω : ManifoldForm (𝓠 n) M n}
    (hω : ContMDiffForm (𝓠 n) 0 ω) (hc : IsCompact (tsupport ω)) :
    integral (-o) ω = -integral o ω := by
  obtain ⟨T, ⟨D⟩⟩ := exists_integrationData ho hc
  rw [integral_eq_integrationData ho.neg hω hc D.neg subset_rfl,
    integral_eq_integrationData ho hω hc D subset_rfl, D.integral_neg]

/-- **Additivity of `∫_M`** for continuous compactly supported forms. -/
theorem integral_add (ho : o.IsContinuous (𝓠 n) ∞) {ω₁ ω₂ : ManifoldForm (𝓠 n) M n}
    (h₁ : ContMDiffForm (𝓠 n) 0 ω₁) (h₂ : ContMDiffForm (𝓠 n) 0 ω₂)
    (hc₁ : IsCompact (tsupport ω₁)) (hc₂ : IsCompact (tsupport ω₂)) :
    integral o (ω₁ + ω₂) = integral o ω₁ + integral o ω₂ := by
  have := integral_finsetSum ho Finset.univ (ω := fun b : Bool => cond b ω₁ ω₂)
    (fun b _ => by cases b <;> assumption) (fun b _ => by cases b <;> assumption)
  simpa [Fintype.sum_bool] using this

/-- **The integral for an oriented atlas**: an oriented atlas `A` of `M` (chart changes with
positive Jacobian, `IsOrientedAtlas`) orients `M` by the tangent orientation reading as the
standard orientation of `ℝⁿ` in its charts, which is continuous; its charts are positive, and a
form supported in a chart `chartAt H x₀ ∈ A` has `∫_M ω = ∫_{x₀} ω`. -/
theorem integral_eq_chartIntegral_of_isOrientedAtlas {A : Set (OpenPartialHomeomorph M
    (EuclideanQuadrant n))} (hA : IsOrientedAtlas (𝓠 n) ∞ A) {ω : ManifoldForm (𝓠 n) M n}
    (hω : ContMDiffForm (𝓠 n) 0 ω) {x₀ : M} (hx₀ : chartAt (EuclideanQuadrant n) x₀ ∈ A)
    {K : Set M} (hK : IsCompact K) (hKe : K ⊆ (chartAt (EuclideanQuadrant n) x₀).source)
    (hω0 : ∀ x ∉ K, ω x = 0) :
    integral (hA.tangentOrientation (stdOrientation n)) ω =
      chartIntegral (chartAt (EuclideanQuadrant n) x₀) ω := by
  rw [integral_eq_chartIntegral (b := true)
    (hA.isContinuous_tangentOrientation (by simp) (stdOrientation n)) hω subset_rfl
    (fun x hx => (hA.orientationIn_tangentOrientation (by simp) (stdOrientation n) hx₀ hx).trans
      (signedOr_true _).symm) hK hKe hω0, orSign_true, one_mul]

end ManifoldForm

end Polyfold
