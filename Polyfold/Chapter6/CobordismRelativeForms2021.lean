import Polyfold.Chapter6.InvariantCobordism2021

/-!
# Forms pulled back along the projection of a product end (2021 Theorem 6.7.1, p. 278)

Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021): in the proof of
Theorem 6.7.1 (p. 277–279; preprint Theorem 6.43) the form `ω − dβ` on the ends `(a, b) × S_i`
of the cobordism `S_F` is the pull-back of a form on `S_i` along the projection.  The form `β`
is only given on `S_i`, as a form on a finite-dimensional manifold, so its pull-back has to be
built on the manifold `S_F`.

Everything is stated for an abstract `(k+1)`-manifold with corners `M` with product ends
(`ProductEnd`, `InvariantProductEnds2021`) over a `k`-manifold `N`:

* `ProductEnd.tailCLM_comp_chartChangeDeriv`: the change between two product charts (of two
  product ends with the same projection to `N`) is, after forgetting the time coordinate, the
  change between the charts of `N`.
* `ProductEnd.pullAt E γ`: the pull-back of a form `γ` on `N` along the projection of `E`,
  given at `p` by its expression `tail^*γ` in the product chart of the chart at the projection
  of `p`.
* `ProductEnd.isEndPullback_of_pullAt`: a form which at each point of a product end `E'` is
  `pullAt` of some product end with the same projection reads as the pull-back of `γ` on `E'`
  (`ProductEnd.IsEndPullback`).
* `ProductEnd.contMDiffForm_smulFun_of_isEndPullback`: a cut-off of such a form is `C^∞`.
* `ProductEnd.IsEndPullback.extDeriv`: `d` of a pull-back is the pull-back of `d`.
* `ProductEnd.IsEndProductOrientation.of_subEnd`: the product orientation passes to a smaller
  product end (the time coordinate of the product charts is translated).
* `exists_glued_extension`: an extension `γ` of face data `−σ` on `M` with `γ = P_i` where the
  cut-off `ρ_i(t)` is `1`, glued from two forms `P₀`, `P₁` with face restriction `−σ` and an
  extension of `−χ(t) σ` (`exists_extension`).

No hypothesis is added; nothing here mentions M-polyfolds.
-/

open Set Filter Topology Manifold Module

noncomputable section

namespace Polyfold

local notation "𝓠" => modelWithCornersEuclideanQuadrant

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

section PullEnd

open ManifoldForm

variable {k : ℕ} {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanQuadrant k) N]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant (k + 1)) M]

/-- Forgetting the time coordinate maps `[0,∞)^{k+1}` into `[0,∞)^k`. -/
theorem mapsTo_tailE_range : MapsTo (tailE (k := k)) (range (𝓠 (k + 1))) (range (𝓠 k)) := by
  rintro _ ⟨q, rfl⟩
  exact ⟨⟨tailE q.1, fun i => q.2 i.succ⟩, rfl⟩

theorem extend_mem_range {X : Type*} [TopologicalSpace X] {n : ℕ}
    (e : OpenPartialHomeomorph X (EuclideanQuadrant n)) (x : X) :
    e.extend (𝓠 n) x ∈ range (𝓠 n) := by
  rw [OpenPartialHomeomorph.extend_coe]; exact mem_range_self _

/-- **The change between two product charts** (proof of 2021 Theorem 6.7.1, p. 278: the ends
of `S_F` are products): for two product ends `E`, `E'` of `M` over `N` with the same projection
to `N`, the derivative of the change from the product chart of `chartAt x` (for `E`) to that of
`chartAt x'` (for `E'`) is, after forgetting the time coordinate, the derivative of the change
from `chartAt x` to `chartAt x'`. -/
theorem ProductEnd.tailCLM_comp_chartChangeDeriv [IsManifold (𝓠 k) ∞ N]
    [IsManifold (𝓠 (k + 1)) ∞ M] {a b a' b' : ℝ} (E : ProductEnd k N M a b)
    (E' : ProductEnd k N M a' b')
    (hφ : ∀ p ∈ E.φ.source ∩ E'.φ.source, (E'.φ p).2 = (E.φ p).2) (x x' : N) {p : M}
    (hp : p ∈ (E.chart (chartAt (EuclideanQuadrant k) x)).source)
    (hp' : p ∈ (E'.chart (chartAt (EuclideanQuadrant k) x')).source) :
    (tailCLM k).comp (chartChangeDeriv (𝓠 (k + 1)) (E.chart (chartAt (EuclideanQuadrant k) x))
        (E'.chart (chartAt (EuclideanQuadrant k) x')) p) =
      (chartChangeDeriv (𝓠 k) (chartAt (EuclideanQuadrant k) x)
        (chartAt (EuclideanQuadrant k) x') (E.φ p).2).comp (tailCLM k) := by
  set c := chartAt (EuclideanQuadrant k) x
  set c' := chartAt (EuclideanQuadrant k) x'
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  obtain ⟨hpE, hqc⟩ := E.mem_chart_source.1 hp
  obtain ⟨hpE', hqc'⟩ := E'.mem_chart_source.1 hp'
  rw [hφ p ⟨hpE, hpE'⟩] at hqc'
  have hty : tailE ((E.chart c).extend (𝓠 (k + 1)) p) = c.extend (𝓠 k) (E.φ p).2 := by
    rw [E.chart_extend_apply hpE, tailE_consE]
  have h1 := hasFDerivWithinAt_chartChangeDeriv hn (E.chart_mem x) (E'.chart_mem x') hp hp'
  have h2 := hasFDerivWithinAt_chartChangeDeriv hn
    (IsManifold.chart_mem_maximalAtlas (I := 𝓠 k) (n := ∞) x)
    (IsManifold.chart_mem_maximalAtlas (I := 𝓠 k) (n := ∞) x') hqc hqc'
  have h3 := (tailCLM k).hasFDerivAt.comp_hasFDerivWithinAt
    ((E.chart c).extend (𝓠 (k + 1)) p) h1
  rw [← hty] at h2
  have h4 := h2.comp ((E.chart c).extend (𝓠 (k + 1)) p) (tailCLM k).hasFDerivWithinAt
    mapsTo_tailE_range
  have hev : ((𝓠 k).extendCoordChange c c' ∘ tailCLM k) =ᶠ[𝓝[range (𝓠 (k + 1))]
      ((E.chart c).extend (𝓠 (k + 1)) p)]
      (tailCLM k ∘ (𝓠 (k + 1)).extendCoordChange (E.chart c) (E'.chart c')) := by
    filter_upwards [(𝓠 (k + 1)).extendCoordChange_source_mem_nhdsWithin' hp hp'] with z hz
    rw [← OpenPartialHomeomorph.extend_image_source_inter] at hz
    obtain ⟨p', ⟨hp1, hp2⟩, rfl⟩ := hz
    obtain ⟨hpE1, hqc1⟩ := E.mem_chart_source.1 hp1
    obtain ⟨hpE1', -⟩ := E'.mem_chart_source.1 hp2
    simp only [Function.comp_apply, ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans,
      tailCLM_apply]
    rw [(E.chart c).extend_left_inv hp1, E'.chart_extend_apply hpE1', tailE_consE,
      E.chart_extend_apply hpE1, tailE_consE, c.extend_left_inv hqc1, hφ p' ⟨hpE1, hpE1'⟩]
  exact ((𝓠 (k + 1)).uniqueDiffOn _ (extend_mem_range _ p)).eq
    h3 (h4.congr_of_eventuallyEq hev.symm
      (hev.symm.self_of_nhdsWithin (extend_mem_range _ p)))

/-- **The pull-back of a form on `N` along the projection of a product end** (the form
`p₁^*β` on the ends of `S_F`, 2021 p. 278): at `p` over `q ∈ N`, the form whose expression in the
product chart of `chartAt q` is `tail^*(γ q)`.  It is meaningful on the end `E.φ.source`. -/
def ProductEnd.pullAt {a b : ℝ} (E : ProductEnd k N M a b) {m : ℕ}
    (γ : ManifoldForm (𝓠 k) N m) : ManifoldForm (𝓠 (k + 1)) M m :=
  fun p => ((tailPull (γ (E.φ p).2 : EuclideanSpace ℝ (Fin k) [⋀^Fin m]→L[ℝ] ℝ)
    ).compContinuousLinearMap (chartChangeDeriv (𝓠 (k + 1)) (chartAt (EuclideanQuadrant (k + 1)) p)
      (E.chart (chartAt (EuclideanQuadrant k) (E.φ p).2)) p) :
    EuclideanSpace ℝ (Fin (k + 1)) [⋀^Fin m]→L[ℝ] ℝ)

variable [IsManifold (𝓠 k) ∞ N] [IsManifold (𝓠 (k + 1)) ∞ M]

/-- **`pullAt` in the product charts of another end**: if `Ω` is `E.pullAt γ` at the point with
coordinates `y` in a product chart of `E'` (two ends with the same projection to `N`), then the
expression of `Ω` at `y` is `tail^*` of the expression of `γ`. -/
theorem ProductEnd.chartForm_eq_of_eq_pullAt {a b a' b' : ℝ} (E : ProductEnd k N M a b)
    (E' : ProductEnd k N M a' b')
    (hφ : ∀ p ∈ E'.φ.source ∩ E.φ.source, (E.φ p).2 = (E'.φ p).2) {m : ℕ}
    {Ω : ManifoldForm (𝓠 (k + 1)) M m} {γ : ManifoldForm (𝓠 k) N m} (y₀ : N)
    {y : EuclideanSpace ℝ (Fin (k + 1))}
    (hy : y ∈ ((E'.chart (chartAt (EuclideanQuadrant k) y₀)).extend (𝓠 (k + 1))).target)
    (hpE : E'.pt (chartAt (EuclideanQuadrant k) y₀) y ∈ E.φ.source)
    (hΩ : Ω (E'.pt (chartAt (EuclideanQuadrant k) y₀) y) =
      E.pullAt γ (E'.pt (chartAt (EuclideanQuadrant k) y₀) y)) :
    chartForm (𝓠 (k + 1)) (E'.chart (chartAt (EuclideanQuadrant k) y₀)) Ω y =
      tailPull (chartForm (𝓠 k) (chartAt (EuclideanQuadrant k) y₀) γ (tailE y)) := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  set c₀ := chartAt (EuclideanQuadrant k) y₀
  obtain ⟨hp', hφp⟩ := E'.pt_mem hy
  have hsymm := E'.chart_extend_symm hy
  have hpE' := (E'.mem_chart_source.1 hp').1
  have hq : ((c₀.extend (𝓠 k)).symm (tailE y)) = (E.φ (E'.pt c₀ y)).2 := by
    rw [hφ _ ⟨hpE', hpE⟩, hφp]
  have hpq : E'.pt c₀ y ∈ (E.chart (chartAt (EuclideanQuadrant k) (E.φ (E'.pt c₀ y)).2)).source :=
    E.mem_chart_source.2 ⟨hpE, _root_.mem_chart_source _ _⟩
  have key := E'.tailCLM_comp_chartChangeDeriv E (fun p hp => hφ p hp) y₀
    (E.φ (E'.pt c₀ y)).2 hp' hpq
  rw [← hφ _ ⟨hpE', hpE⟩] at key
  ext v
  rw [chartForm_apply, tailPull_apply, chartForm_apply, hsymm, hq, hΩ]
  change γ (E.φ (E'.pt c₀ y)).2 (fun j => tailE (chartChangeDeriv (𝓠 (k + 1))
    (chartAt (EuclideanQuadrant (k + 1)) (E'.pt c₀ y))
    (E.chart (chartAt (EuclideanQuadrant k) (E.φ (E'.pt c₀ y)).2)) (E'.pt c₀ y)
    (chartChangeDeriv (𝓠 (k + 1)) (E'.chart c₀)
      (chartAt (EuclideanQuadrant (k + 1)) (E'.pt c₀ y)) (E'.pt c₀ y) (v j)))) = _
  congr 1
  funext j
  rw [chartChangeDeriv_comp_apply hn (E'.chart_mem y₀)
    (IsManifold.chart_mem_maximalAtlas (E'.pt c₀ y)) (E.chart_mem _) hp'
    (_root_.mem_chart_source _ _) hpq]
  exact congrArg (fun L : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] EuclideanSpace ℝ (Fin k) => L (v j))
    key

/-- **A form which is `pullAt` at each point of a product end reads as the pull-back** of `γ`
on it (`IsEndPullback`), the defining ends having the same projection to `N`. -/
theorem ProductEnd.isEndPullback_of_pullAt {a' b' : ℝ} (E' : ProductEnd k N M a' b') {m : ℕ}
    {Ω : ManifoldForm (𝓠 (k + 1)) M m} {γ : ManifoldForm (𝓠 k) N m}
    (h : ∀ p ∈ E'.φ.source, ∃ (a b : ℝ) (E : ProductEnd k N M a b), p ∈ E.φ.source ∧
      (∀ p' ∈ E'.φ.source ∩ E.φ.source, (E.φ p').2 = (E'.φ p').2) ∧ Ω p = E.pullAt γ p) :
    E'.IsEndPullback Ω γ := by
  intro y₀ y hy
  obtain ⟨a, b, E, hpE, hφ, hΩ⟩ := h _ (E'.mem_chart_source.1 (E'.pt_mem hy).1).1
  exact E.chartForm_eq_of_eq_pullAt E' hφ y₀ hy hpE hΩ

omit [IsManifold (𝓠 k) ∞ N] [IsManifold (𝓠 (k + 1)) ∞ M] in
/-- A form reading as the pull-back of a `C^r` form is `C^r` in the product charts. -/
theorem ProductEnd.IsEndPullback.contDiffOn_chartForm {a b : ℝ} {E : ProductEnd k N M a b}
    {m : ℕ} {Ω : ManifoldForm (𝓠 (k + 1)) M m} {γ : ManifoldForm (𝓠 k) N m}
    (h : E.IsEndPullback Ω γ) {r : WithTop ℕ∞} (hγ : ContMDiffForm (𝓠 k) r γ) (y₀ : N) :
    ContDiffOn ℝ r (chartForm (𝓠 (k + 1)) (E.chart (chartAt (EuclideanQuadrant k) y₀)) Ω)
      ((E.chart (chartAt (EuclideanQuadrant k) y₀)).extend (𝓠 (k + 1))).target := by
  have h1 : ContDiffOn ℝ r (fun y : EuclideanSpace ℝ (Fin (k + 1)) =>
      chartForm (𝓠 k) (chartAt (EuclideanQuadrant k) y₀) γ (tailCLM k y))
      ((E.chart (chartAt (EuclideanQuadrant k) y₀)).extend (𝓠 (k + 1))).target :=
    (hγ y₀).comp (tailCLM k).contDiff.contDiffOn fun y hy => (E.mem_chart_extend_target.1 hy).2
  exact ((ContinuousAlternatingMap.compContinuousLinearMapCLM (tailCLM k)).contDiff.comp_contDiffOn
    h1).congr fun y hy => by rw [h y₀ y hy]; rfl

omit [IsManifold (𝓠 k) ∞ N] in
/-- **A cut-off of a pull-back is `C^∞`**: if near every point of the support of the smooth
function `f` the form `Ω` reads as the pull-back of the `C^∞` form `γ` on some product end, then
`f Ω` is a `C^∞` form on `M`. -/
theorem ProductEnd.contMDiffForm_smulFun_of_isEndPullback {m : ℕ}
    {Ω : ManifoldForm (𝓠 (k + 1)) M m} {γ : ManifoldForm (𝓠 k) N m}
    (hγ : ContMDiffForm (𝓠 k) ∞ γ) {f : M → ℝ} (hf : ContMDiff (𝓠 (k + 1)) 𝓘(ℝ) ∞ f)
    (h : ∀ p ∈ _root_.tsupport f, ∃ (a b : ℝ) (E : ProductEnd k N M a b), p ∈ E.φ.source ∧
      E.IsEndPullback Ω γ) :
    ContMDiffForm (𝓠 (k + 1)) ∞ (smulFun f Ω) := by
  refine contMDiffForm_of_local le_rfl fun p => ?_
  by_cases hp : p ∈ _root_.tsupport f
  · obtain ⟨a, b, E, hpE, hpull⟩ := h p hp
    set e := E.chart (chartAt (EuclideanQuadrant k) (E.φ p).2)
    have he : e ∈ IsManifold.maximalAtlas (𝓠 (k + 1)) ∞ M := E.chart_mem _
    have hpe : p ∈ e.source := E.mem_chart_source.2 ⟨hpE, _root_.mem_chart_source _ _⟩
    refine ⟨e, he, hpe, ?_⟩
    have hT := e.extend_target_mem_nhdsWithin (I := 𝓠 (k + 1)) hpe
    have hmem : e.extend (𝓠 (k + 1)) p ∈ (e.extend (𝓠 (k + 1))).target :=
      (e.extend (𝓠 (k + 1))).map_source (by rw [e.extend_source]; exact hpe)
    have hρ' : ContDiffWithinAt ℝ ∞ (f ∘ (e.extend (𝓠 (k + 1))).symm) (range (𝓠 (k + 1)))
        (e.extend (𝓠 (k + 1)) p) := by
      have := contMDiffOn_iff_contDiffOn.1 (hf.comp_contMDiffOn (contMDiffOn_extend_symm he))
      rw [← e.extend_target'] at this
      exact (this _ hmem).mono_of_mem_nhdsWithin hT
    have hη' : ContDiffWithinAt ℝ ∞ (chartForm (𝓠 (k + 1)) e Ω) (range (𝓠 (k + 1)))
        (e.extend (𝓠 (k + 1)) p) :=
      ((hpull.contDiffOn_chartForm hγ _) _ hmem).mono_of_mem_nhdsWithin hT
    refine (hρ'.smul hη').congr_of_eventuallyEq ?_ ?_
    · filter_upwards with z
      rw [chartForm_smulFun]
      rfl
    · rw [chartForm_smulFun]
      rfl
  · refine ⟨chartAt _ p, IsManifold.chart_mem_maximalAtlas p, _root_.mem_chart_source _ p, ?_⟩
    refine contDiffWithinAt_chartForm_of_eventually_eq_zero ?_ (_root_.mem_chart_source _ p)
    filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hp] with q hq
    rw [smulFun_apply, hq, Pi.zero_apply, zero_smul]

/-- **`d` of a pull-back is the pull-back of `d`** on a product end: if `Ω` reads as the
pull-back of `γ` (`IsEndPullback`), both `C¹`, then `dΩ` reads as the pull-back of `dγ`. -/
theorem ProductEnd.IsEndPullback.extDeriv {a b : ℝ} {E : ProductEnd k N M a b} {m : ℕ}
    {Ω : ManifoldForm (𝓠 (k + 1)) M m} {γ : ManifoldForm (𝓠 k) N m}
    (h : E.IsEndPullback Ω γ) (hΩ : ContMDiffForm (𝓠 (k + 1)) 1 Ω)
    (hγ : ContMDiffForm (𝓠 k) 1 γ) :
    E.IsEndPullback (ManifoldForm.extDeriv Ω) (ManifoldForm.extDeriv γ) := by
  intro y₀ y hy
  set c₀ := chartAt (EuclideanQuadrant k) y₀
  have hc₀ := IsManifold.chart_mem_maximalAtlas (I := 𝓠 k) (n := ∞) y₀
  have hT := (E.mem_chart_extend_target.1 hy).2
  have hyr : y ∈ range (𝓠 (k + 1)) := (E.chart c₀).extend_target_subset_range hy
  have hTn : ((E.chart c₀).extend (𝓠 (k + 1))).target ∈ 𝓝[range (𝓠 (k + 1))] y := by
    have := (E.chart c₀).extend_target_mem_nhdsWithin (I := 𝓠 (k + 1)) (E.pt_mem hy).1
    rwa [← E.chart_extend_symm hy, ((E.chart c₀).extend (𝓠 (k + 1))).right_inv hy] at this
  have hfd : ∀ z ∈ range (𝓠 (k + 1)),
      fderivWithin ℝ (tailE (k := k)) (range (𝓠 (k + 1))) z = tailCLM k := fun z hz =>
    (tailCLM k).hasFDerivWithinAt.fderivWithin ((𝓠 (k + 1)).uniqueDiffOn z hz)
  have hev : chartForm (𝓠 (k + 1)) (E.chart c₀) Ω =ᶠ[𝓝[range (𝓠 (k + 1))] y]
      formPullback tailE (fderivWithin ℝ (tailE (k := k)) (range (𝓠 (k + 1))))
        (chartForm (𝓠 k) c₀ γ) := by
    filter_upwards [hTn] with z hz
    rw [h y₀ z hz, formPullback, hfd z ((E.chart c₀).extend_target_subset_range hz)]
  rw [chartForm_extDeriv_of_mem_target (E.chart_mem y₀) hΩ hy,
    extDerivWithin_extend_target _ _ hy,
    extDerivWithin_eq_formPullback (r := ∞) hev (hγ.differentiableWithinAt le_rfl y₀ hT)
      (tailCLM k).contDiff.contDiffWithinAt (by norm_cast) (𝓠 (k + 1)).uniqueDiffOn
      ((𝓠 (k + 1)).range_subset_closure_interior hyr) hyr mapsTo_tailE_range,
    formPullback, hfd y hyr, chartForm_extDeriv_of_mem_target hc₀ hγ hT,
    extDerivWithin_extend_target _ _ hT]

/-! ### The product orientation on a smaller end -/

/-- Two charts which differ by a translation near `x` have the same derivative relative to a
third chart. -/
theorem chartChangeDeriv_eq_of_eventually_add_const {n : ℕ} {X : Type*} [TopologicalSpace X]
    (c e e' : OpenPartialHomeomorph X (EuclideanQuadrant n)) {x : X} (hx : x ∈ c.source)
    (δ : EuclideanSpace ℝ (Fin n))
    (h : ∀ᶠ p in 𝓝 x, e'.extend (𝓠 n) p = e.extend (𝓠 n) p + δ) :
    chartChangeDeriv (𝓠 n) c e' x = chartChangeDeriv (𝓠 n) c e x := by
  unfold chartChangeDeriv
  have hev : (𝓠 n).extendCoordChange c e' =ᶠ[𝓝[range (𝓠 n)] (c.extend (𝓠 n) x)]
      fun z => (𝓠 n).extendCoordChange c e z + δ := by
    filter_upwards [nhdsWithin_le_nhds (c.extend_preimage_mem_nhds (I := 𝓠 n) hx h)] with z hz
    simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply]
    exact hz
  rw [hev.fderivWithin_eq (hev.self_of_nhdsWithin (extend_mem_range c x))]
  exact fderivWithin_add_const δ

omit [IsManifold (𝓠 k) ∞ N] [IsManifold (𝓠 (k + 1)) ∞ M] in
/-- **The product orientation on a smaller end**: if `M` carries the product orientation
`e ∧ o_N` on the product end `E` (`IsEndProductOrientation`), it does on every product end `E'`
inside `E` with the same identification (the product charts of `E'` are those of `E` up to a
translation of the time coordinate). -/
theorem ProductEnd.IsEndProductOrientation.of_subEnd {a b a' b' : ℝ} {E : ProductEnd k N M a b}
    {E' : ProductEnd k N M a' b'} {oM : TangentOrientation (𝓠 (k + 1)) M (k + 1)}
    {oN : TangentOrientation (𝓠 k) N k} (hor : E.IsEndProductOrientation oM oN)
    (hsub : E'.φ.source ⊆ E.φ.source) (hφ : ∀ p ∈ E'.φ.source, E'.φ p = E.φ p) :
    E'.IsEndProductOrientation oM oN := by
  intro y₀ x hx
  set c₀ := chartAt (EuclideanQuadrant k) y₀
  obtain ⟨hxE', hxc⟩ := E'.mem_chart_source.1 hx
  have hxE : x ∈ (E.chart c₀).source :=
    E.mem_chart_source.2 ⟨hsub hxE', by rw [← hφ x hxE']; exact hxc⟩
  have hd : chartChangeDeriv (𝓠 (k + 1)) (chartAt (EuclideanQuadrant (k + 1)) x) (E'.chart c₀) x =
      chartChangeDeriv (𝓠 (k + 1)) (chartAt (EuclideanQuadrant (k + 1)) x) (E.chart c₀) x := by
    refine chartChangeDeriv_eq_of_eventually_add_const _ _ _ (_root_.mem_chart_source _ x)
      (consE (a - a') 0) ?_
    filter_upwards [E'.φ.open_source.mem_nhds hxE'] with p hp
    rw [E'.chart_extend_apply hp, E.chart_extend_apply (hsub hp), hφ p hp]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  rw [hφ x hxE']
  have := hor y₀ x hxE
  unfold orientationIn at this ⊢
  rwa [hd]

omit [IsManifold (𝓠 k) ∞ N] [IsManifold (𝓠 (k + 1)) ∞ M] in
/-- `IsEndPullback` only depends on the values of the form on the end. -/
theorem ProductEnd.IsEndPullback.congr {a b : ℝ} {E : ProductEnd k N M a b} {m : ℕ}
    {Ω Ω' : ManifoldForm (𝓠 (k + 1)) M m} {γ : ManifoldForm (𝓠 k) N m}
    (h : E.IsEndPullback Ω γ) (hΩ : ∀ p ∈ E.φ.source, Ω' p = Ω p) : E.IsEndPullback Ω' γ := by
  intro y₀ y hy
  rw [← h y₀ y hy]
  ext v
  rw [chartForm_apply, chartForm_apply, E.chart_extend_symm hy,
    hΩ _ (E.mem_chart_source.1 (E.pt_mem hy).1).1]

omit [IsManifold (𝓠 k) ∞ N] [IsManifold (𝓠 (k + 1)) ∞ M] in
/-- `IsEndPullback` is additive. -/
theorem ProductEnd.IsEndPullback.add {a b : ℝ} {E : ProductEnd k N M a b} {m : ℕ}
    {Ω Ω' : ManifoldForm (𝓠 (k + 1)) M m} {γ γ' : ManifoldForm (𝓠 k) N m}
    (h : E.IsEndPullback Ω γ) (h' : E.IsEndPullback Ω' γ') :
    E.IsEndPullback (Ω + Ω') (γ + γ') := by
  intro y₀ y hy
  rw [chartForm_add, chartForm_add, Pi.add_apply, Pi.add_apply, h y₀ y hy, h' y₀ y hy]
  ext v
  rfl

end PullEnd

/-! ### Gluing an extension of face data from two ends -/

section Glue

open ManifoldForm

variable {n d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant (n + 1)) M]
  [IsManifold (𝓠 (n + 1)) ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- **An extension of face data with prescribed values on two ends** (the form `β` on `S_F` with
`j^*β = p₁^*τ` and `β = p₁^*β_i` on the ends, proof of 2021 Theorem 6.7.1, p. 278): let `σ` be a
form on the faces of `M`, `t : M → ℝ` a smooth function with compact slabs, `ρ₀`, `ρ₁` smooth
functions of `t` with `ρ₀ + ρ₁ = 1` outside `[l, u]`, and `P₀`, `P₁` forms on `M` such that
`ρ_i(t) P_i` is `C^∞` and the face restriction of `P_i` is `−σ` where `ρ_i(t) ≠ 0`.  Then there
is a `C^∞` form `γ` on `M` whose face restriction is `−σ`, with `γ = P₀` where `ρ₀ = 1`, `ρ₁ = 0`
and `γ = P₁` where `ρ₁ = 1`, `ρ₀ = 0`: `γ = ρ₀ P₀ + ρ₁ P₁ + (1 − ρ₀ − ρ₁) γ_mid` with `γ_mid` an
extension of `−χ(t) σ` (`exists_extension`), `χ` a cut-off equal to `1` on `[l, u]`. -/
theorem exists_glued_extension {t : M → ℝ} (ht : ContMDiff (𝓠 (n + 1)) 𝓘(ℝ) ∞ t)
    (hslab : ∀ c c' : ℝ, IsCompact {p : M | t p ∈ Icc c c'}) {σ : FaceFormData M n d}
    (hσ : IsChartFaceForm σ) {P₀ P₁ : ManifoldForm (𝓠 (n + 1)) M d} {ρ₀ ρ₁ : ℝ → ℝ}
    (hρ₀ : ContDiff ℝ ∞ ρ₀) (hρ₁ : ContDiff ℝ ∞ ρ₁)
    (hP₀ : ContMDiffForm (𝓠 (n + 1)) ∞ (smulFun (fun p => ρ₀ (t p)) P₀))
    (hP₁ : ContMDiffForm (𝓠 (n + 1)) ∞ (smulFun (fun p => ρ₁ (t p)) P₁))
    (hf₀ : ∀ x i, ∀ u ∈ openFaceDomain (chartAt (EuclideanQuadrant (n + 1)) x) i,
      ρ₀ (t (facePoint (chartAt (EuclideanQuadrant (n + 1)) x) i u)) ≠ 0 →
        faceRestriction P₀ x i u = ((-1 : ℝ) • σ) x i u)
    (hf₁ : ∀ x i, ∀ u ∈ openFaceDomain (chartAt (EuclideanQuadrant (n + 1)) x) i,
      ρ₁ (t (facePoint (chartAt (EuclideanQuadrant (n + 1)) x) i u)) ≠ 0 →
        faceRestriction P₁ x i u = ((-1 : ℝ) • σ) x i u)
    {l u : ℝ} (hmid : ∀ s, s ∉ Icc l u → ρ₀ s + ρ₁ s = 1) :
    ∃ γ : ManifoldForm (𝓠 (n + 1)) M d, ContMDiffForm (𝓠 (n + 1)) ∞ γ ∧
      IsExtendedBy ((-1 : ℝ) • σ) γ ∧
      (∀ p, ρ₀ (t p) = 1 → ρ₁ (t p) = 0 → γ p = P₀ p) ∧
      ∀ p, ρ₁ (t p) = 1 → ρ₀ (t p) = 0 → γ p = P₁ p := by
  set χ : ℝ → ℝ := fun s => cutRise (l - 1) l s * (1 - cutRise u (u + 1) s) with hχ
  have hχs : ContDiff ℝ ∞ χ :=
    (contDiff_cutRise _ _).mul (contDiff_const.sub (contDiff_cutRise _ _))
  have hχ1 : ∀ s ∈ Icc l u, χ s = 1 := fun s hs => by
    simp only [hχ]
    rw [cutRise_eq_one (by linarith) (by linarith [hs.1]),
      cutRise_eq_zero (by linarith) (by linarith [hs.2])]
    norm_num
  have hχ0 : ∀ s, s ∉ Icc (l - 1) (u + 1) → χ s = 0 := fun s hs => by
    simp only [hχ]
    rcases not_and_or.1 hs with h | h
    · rw [cutRise_eq_zero (by linarith) (by linarith [not_le.1 h]), zero_mul]
    · rw [cutRise_eq_one (a := u) (by linarith) (by linarith [not_le.1 h]), sub_self, mul_zero]
  have hχc : HasCompactSupport fun p => χ (t p) :=
    (hslab _ _).of_isClosed_subset isClosed_closure (tsupport_comp_subset ht.continuous hχ0)
  have hσχ : IsChartFaceForm ((-1 : ℝ) • smulFace (fun p => χ (t p)) σ) :=
    (chartFaceForms M n d).smul_mem (-1)
      (isChartFaceForm_smulFace (hχs.contMDiff.comp ht) hσ)
  obtain ⟨γm, hγm, -, hext⟩ := exists_extension hσχ
    ((hasCompactFaceSupport_smulFace hχc σ).smul (-1))
  have hr₂ : ContMDiff (𝓠 (n + 1)) 𝓘(ℝ) ∞ fun p => 1 - ρ₀ (t p) - ρ₁ (t p) :=
    (contMDiff_const.sub (hρ₀.contMDiff.comp ht)).sub (hρ₁.contMDiff.comp ht)
  set γ : ManifoldForm (𝓠 (n + 1)) M d := smulFun (fun p => ρ₀ (t p)) P₀ +
    smulFun (fun p => ρ₁ (t p)) P₁ + smulFun (fun p => 1 - ρ₀ (t p) - ρ₁ (t p)) γm with hγ_def
  have hγ : ContMDiffForm (𝓠 (n + 1)) ∞ γ := (hP₀.add hP₁).add (hγm.smulFun le_rfl hr₂)
  refine ⟨γ, hγ, ?_, fun p h0 h1 => ?_, fun p h1 h0 => ?_⟩
  · refine isExtendedBy_of_openFaceDomain
      (fun x i => ((hσ.smooth x i).continuousOn.const_smul (-1 : ℝ)))
      (hγ.of_le (by norm_num)) fun x i v hv => ?_
    set p := facePoint (chartAt (EuclideanQuadrant (n + 1)) x) i v with hp
    have h0 : ρ₀ (t p) • faceRestriction P₀ x i v = ρ₀ (t p) • ((-1 : ℝ) • σ) x i v := by
      by_cases h : ρ₀ (t p) = 0
      · rw [h, zero_smul, zero_smul]
      · rw [hf₀ x i v hv h]
    have h1 : ρ₁ (t p) • faceRestriction P₁ x i v = ρ₁ (t p) • ((-1 : ℝ) • σ) x i v := by
      by_cases h : ρ₁ (t p) = 0
      · rw [h, zero_smul, zero_smul]
      · rw [hf₁ x i v hv h]
    have h2 : (1 - ρ₀ (t p) - ρ₁ (t p)) • faceRestriction γm x i v =
        (1 - ρ₀ (t p) - ρ₁ (t p)) • ((-1 : ℝ) • σ) x i v := by
      rw [hext x i (openFaceDomain_subset _ _ hv)]
      by_cases h : t p ∈ Icc l u
      · simp only [Pi.smul_apply, smulFace]
        rw [← hp, hχ1 _ h, one_smul]
      · rw [show 1 - ρ₀ (t p) - ρ₁ (t p) = 0 by linarith [hmid _ h], zero_smul, zero_smul]
    have hsum : faceRestriction γ x i v = ρ₀ (t p) • faceRestriction P₀ x i v +
        ρ₁ (t p) • faceRestriction P₁ x i v +
        (1 - ρ₀ (t p) - ρ₁ (t p)) • faceRestriction γm x i v := by
      rw [hγ_def, faceRestriction_add, faceRestriction_add, faceRestriction_smulFun,
        faceRestriction_smulFun, faceRestriction_smulFun]
      rfl
    rw [hsum, h0, h1, h2, ← add_smul, ← add_smul]
    rw [show ρ₀ (t p) + ρ₁ (t p) + (1 - ρ₀ (t p) - ρ₁ (t p)) = 1 by ring, one_smul]
  · simp only [hγ_def, Pi.add_apply, smulFun_apply, h0, h1]
    rw [one_smul, zero_smul, sub_self, sub_zero, zero_smul, add_zero, add_zero]
  · simp only [hγ_def, Pi.add_apply, smulFun_apply, h0, h1]
    rw [one_smul, zero_smul, sub_zero, sub_self, zero_smul, zero_add, add_zero]

end Glue

end Polyfold
