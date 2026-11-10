import Polyfold.Chapter4.EuclideanForms2021
import Polyfold.Chapter6.ManifoldOrientation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021): differential forms on a
finite-dimensional manifold with boundary with corners and their exterior derivative, the global
layer under **Theorem 4.4.7** (p. 199; preprint Theorem 4.28, Stokes' theorem, gap G.40) and
**Theorem 6.7.1** (p. 277).  Numbers and pages are the 2021 text's.

# Forms on a Mathlib manifold with corners

## What is formalized

* **Naturality of `d` on `ℝⁿ`** (`extDerivWithin_formPullback`, its local form
  `extDerivWithin_eq_formPullback`): `d(φ^*ω) = φ^*(dω)` for a `C²` map `φ` within a set with
  unique derivatives (the second derivatives of `φ` cancel by symmetry); this is Mathlib's
  `extDerivWithin_pullback` in the notation `formPullback` of `EuclideanForms2021.lean`.
* `ManifoldForm I M k := (x : M) → TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ`: a `k`-form on a manifold
  with corners `M` modelled on `I : ModelWithCorners ℝ E H` (no regularity).  Mathlib's tangent
  space `T_xM` is the model space `E`, the tangent vectors being read in the chart `chartAt H x`.
* `ManifoldForm.chartForm I e ω`: the expression of `ω` in a chart `e`, the form on `E`
  `y ↦ ω(x)(D(c ∘ e⁻¹)(y) ·, …)`, `x = e⁻¹(y)`, `c = chartAt H x`: the pull-back of `ω` by the
  inverse of the chart, its derivative read in the chart `c` in which `T_xM` is expressed
  (`chartChangeDeriv`, `Chapter6/ManifoldOrientation.lean`).  The change of charts is the
  pull-back by the chart change (`chartForm_eventuallyEq_formPullback`).
* `ManifoldForm.ContMDiffForm I r ω`: `ω` is `C^r`, i.e. its expressions in the charts `chartAt`
  of the atlas are `C^r` on the chart targets.  The support `ManifoldForm.support` and the closed
  support `ManifoldForm.tsupport`.
* **The exterior derivative on `M`** (`ManifoldForm.extDeriv`): `(dω)(x)` is `d` of the expression
  of `ω` in the chart at `x`, within `range I`, at `x`.  **Chart independence**
  (`chartForm_extDeriv`): in every chart `e` of the maximal atlas, the expression of `dω` is `d` of
  the expression of `ω`, for a `C¹` form on a `C^∞` manifold.  `d` is linear on `C¹` forms
  (`extDeriv_add`, `extDeriv_finsetSum`), local (`extDeriv_eq_zero_of_eventually_eq_zero`,
  `tsupport_extDeriv_subset`), and `dω` is continuous in the charts for `C¹` forms
  (`contMDiffForm_zero_extDeriv`).
* Multiplication by functions (`ManifoldForm.smulFun`), with `chartForm_smulFun` and
  `ContMDiffForm.smulFun`.

## The choices

The regularity of a form is read in the charts `chartAt H x` of the atlas (as Mathlib's `ContMDiff`
is), and `d` is defined in those charts; `chartForm_extDeriv` shows that the result reads the same
in every chart of the maximal atlas.  `d` is Mathlib's `extDerivWithin`,
`dω(v₀, …, vₖ) = ∑ (-1)ⁱ Dω(vᵢ)(v₀, …, v̂ᵢ, …, vₖ)` (forms as alternating maps, no factorials).
-/

open Set Filter Topology Manifold Module

/-- Smoothness `C^∞` (Mathlib's `∞` of the scope `ContDiff`, which also makes `ω` a notation). -/
local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

noncomputable section

namespace Polyfold

/-! ### Naturality of the exterior derivative on normed spaces -/

section Naturality

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] {k : ℕ}

/-- **Naturality of the exterior derivative**: `d(φ^*ω) = φ^*(dω)` for a `C²` map `φ` within a set
`s` with unique derivatives, at a point of `s ∩ closure (interior s)`, where `φ` maps `s` to `t`;
the pull-back by `φ` uses the derivative of `φ` within `s`.  (The second derivative of `φ` enters
`d(φ^*ω)` as an alternating sum of the symmetric bilinear map `D²φ(x)`, which vanishes; Mathlib's
`extDerivWithin_pullback`.) -/
theorem extDerivWithin_formPullback {ω : F → F [⋀^Fin k]→L[ℝ] G} {φ : E → F} {s : Set E}
    {t : Set F} {x : E} {r : WithTop ℕ∞} (hω : DifferentiableWithinAt ℝ ω t (φ x))
    (hφ : ContDiffWithinAt ℝ r φ s x) (hr : 2 ≤ r) (hs : UniqueDiffOn ℝ s)
    (hxc : x ∈ closure (interior s)) (hxs : x ∈ s) (hst : MapsTo φ s t) :
    extDerivWithin (formPullback φ (fderivWithin ℝ φ s) ω) s x =
      formPullback φ (fderivWithin ℝ φ s) (extDerivWithin ω t) x :=
  extDerivWithin_pullback hω hφ (by simpa using hr) hs hxc hxs hst

/-- **Naturality of `d`, local form**: if `η` agrees near `x` within `s` with the pull-back `φ^*ω`,
then `dη(x) = φ^*(dω)(x)`. -/
theorem extDerivWithin_eq_formPullback {η : E → E [⋀^Fin k]→L[ℝ] G} {ω : F → F [⋀^Fin k]→L[ℝ] G}
    {φ : E → F} {s : Set E} {t : Set F} {x : E} {r : WithTop ℕ∞}
    (hη : η =ᶠ[𝓝[s] x] formPullback φ (fderivWithin ℝ φ s) ω)
    (hω : DifferentiableWithinAt ℝ ω t (φ x))
    (hφ : ContDiffWithinAt ℝ r φ s x) (hr : 2 ≤ r) (hs : UniqueDiffOn ℝ s)
    (hxc : x ∈ closure (interior s)) (hxs : x ∈ s) (hst : MapsTo φ s t) :
    extDerivWithin η s x = formPullback φ (fderivWithin ℝ φ s) (extDerivWithin ω t) x := by
  rw [hη.extDerivWithin_eq_of_mem hxs]
  exact extDerivWithin_formPullback hω hφ hr hs hxc hxs hst

end Naturality

/-! ### Forms on a manifold and their expressions in charts -/

section Forms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] (k : ℕ)

/-- **A `k`-form on a manifold with corners** `M` modelled on `I`: a continuous alternating
`k`-linear form on every tangent space `T_xM` (Mathlib's `TangentSpace I x`, which is the model
space `E`, the tangent vectors read in the chart `chartAt H x`).  No regularity is required; see
`ManifoldForm.ContMDiffForm`. -/
abbrev ManifoldForm : Type _ := (x : M) → TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ

variable {I M k}

namespace ManifoldForm

/-- **The expression of a form in a chart** `e`: the form on `E`
`y ↦ ω(x)(D(c ∘ e⁻¹)(y) v₀, …, D(c ∘ e⁻¹)(y) vₖ₋₁)`, `x = e⁻¹(y)`, `c = chartAt H x`, i.e. the
pull-back of `ω` by the inverse of the chart, whose derivative at `y` is read in the chart `c` in
which `T_xM` is expressed.  It is meaningful on the chart target `(e.extend I).target`. -/
def chartForm (I : ModelWithCorners ℝ E H) (e : OpenPartialHomeomorph M H) (ω : ManifoldForm I M k)
    (y : E) : E [⋀^Fin k]→L[ℝ] ℝ :=
  (ω ((e.extend I).symm y)).compContinuousLinearMap
    (chartChangeDeriv I e (chartAt H ((e.extend I).symm y)) ((e.extend I).symm y))

theorem chartForm_apply (e : OpenPartialHomeomorph M H) (ω : ManifoldForm I M k) (y : E)
    (v : Fin k → E) :
    chartForm I e ω y v = ω ((e.extend I).symm y)
      (chartChangeDeriv I e (chartAt H ((e.extend I).symm y)) ((e.extend I).symm y) ∘ v) := rfl

/-- In the chart at `x`, at the point `x`, the expression of `ω` is `ω(x)` itself. -/
theorem chartForm_extChartAt_self (ω : ManifoldForm I M k) (x : M) :
    chartForm I (chartAt H x) ω (extChartAt I x x) = ω x := by
  ext v
  rw [chartForm_apply, ← extChartAt, (extChartAt I x).left_inv (mem_extChartAt_source x),
    chartChangeDeriv_self (mem_chart_source H x)]
  rfl

/-- The expression of a sum is the sum of the expressions. -/
theorem chartForm_add (e : OpenPartialHomeomorph M H) (ω₁ ω₂ : ManifoldForm I M k) :
    chartForm I e (ω₁ + ω₂) = chartForm I e ω₁ + chartForm I e ω₂ := by
  funext y; ext v; rfl

@[simp]
theorem chartForm_zero (e : OpenPartialHomeomorph M H) :
    chartForm I e (0 : ManifoldForm I M k) = 0 := by
  funext y; ext v; rfl

theorem chartForm_finsetSum {ι : Type*} (u : Finset ι) (e : OpenPartialHomeomorph M H)
    (ω : ι → ManifoldForm I M k) :
    chartForm I e (∑ j ∈ u, ω j) = ∑ j ∈ u, chartForm I e (ω j) := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | insert j u hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, chartForm_add, ih]

/-- **The product of a form with a function** `f : M → ℝ`: `(f ω)(x) = f(x) ω(x)`. -/
def smulFun (f : M → ℝ) (ω : ManifoldForm I M k) : ManifoldForm I M k := fun x => f x • ω x

theorem smulFun_apply (f : M → ℝ) (ω : ManifoldForm I M k) (x : M) :
    smulFun f ω x = f x • ω x := rfl

theorem chartForm_smulFun (e : OpenPartialHomeomorph M H) (f : M → ℝ) (ω : ManifoldForm I M k)
    (y : E) : chartForm I e (smulFun f ω) y = f ((e.extend I).symm y) • chartForm I e ω y := by
  ext v; rfl

/-- `∑ⱼ fⱼ ω = (∑ⱼ fⱼ) ω`. -/
theorem finsetSum_smulFun {ι : Type*} (u : Finset ι) (f : ι → M → ℝ) (ω : ManifoldForm I M k) :
    ∑ j ∈ u, smulFun (f j) ω = smulFun (fun x => ∑ j ∈ u, f j x) ω := by
  funext x
  simp only [Finset.sum_apply, smulFun_apply, Finset.sum_smul]

/-! #### The support -/

/-- The support of a form: the points where it does not vanish. -/
def support (ω : ManifoldForm I M k) : Set M := {x | ω x ≠ 0}

/-- The closed support of a form. -/
def tsupport (ω : ManifoldForm I M k) : Set M := closure (support ω)

theorem eq_zero_of_notMem_tsupport {ω : ManifoldForm I M k} {x : M} (hx : x ∉ tsupport ω) :
    ω x = 0 := by
  by_contra h
  exact hx (subset_closure h)

theorem support_smulFun_subset (f : M → ℝ) (ω : ManifoldForm I M k) :
    support (smulFun f ω) ⊆ Function.support f ∩ support ω := fun x hx => by
  refine ⟨fun h => hx ?_, fun h => hx ?_⟩ <;> simp [smulFun_apply, h]

theorem tsupport_smulFun_subset (f : M → ℝ) (ω : ManifoldForm I M k) :
    tsupport (smulFun f ω) ⊆ _root_.tsupport f ∩ tsupport ω :=
  (closure_mono (support_smulFun_subset f ω)).trans (closure_inter_subset_inter_closure _ _)

/-- A form vanishing outside a set `K`, with `K` inside the source of a chart `e`, has expression
`0` in `e` at the points of the target outside `e(K)`. -/
theorem chartForm_eq_zero_of_notMem {ω : ManifoldForm I M k} {K : Set M}
    (hK : ∀ x ∉ K, ω x = 0) (e : OpenPartialHomeomorph M H) {y : E}
    (hy : (e.extend I).symm y ∉ K) : chartForm I e ω y = 0 := by
  ext v
  rw [chartForm_apply, hK _ hy]
  rfl

/-! #### The change of charts -/

section ChartChange

variable [IsManifold I ∞ M]

/-- **The change of charts for the expression of a form**: at a point `e(x)` of the overlap, the
expression in `e` is the pull-back of the expression in `e'` by the chart change
`e' ∘ e⁻¹` (`I.extendCoordChange e e'`), with its derivative within `range I`. -/
theorem chartForm_eq_formPullback {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) (he' : e' ∈ IsManifold.maximalAtlas I ∞ M)
    (ω : ManifoldForm I M k) {x : M} (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    chartForm I e ω (e.extend I x) =
      formPullback (I.extendCoordChange e e') (fderivWithin ℝ (I.extendCoordChange e e') (range I))
        (chartForm I e' ω) (e.extend I x) := by
  have hfx : I.extendCoordChange e e' (e.extend I x) = e'.extend I x := by
    simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply]
    rw [e.extend_left_inv hx]
  have hc := IsManifold.chart_mem_maximalAtlas (I := I) (n := ∞) x
  ext v
  rw [formPullback_apply, hfx, chartForm_apply, chartForm_apply, e.extend_left_inv hx,
    e'.extend_left_inv hx']
  congr 1
  funext j
  exact (chartChangeDeriv_comp_apply (by simp) he he' hc hx hx' (mem_chart_source H x) _).symm

/-- **The change of charts, near a point**: the expression in `e` agrees near `e(x)` within
`range I` with the pull-back of the expression in `e'` by the chart change. -/
theorem chartForm_eventuallyEq_formPullback {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) (he' : e' ∈ IsManifold.maximalAtlas I ∞ M)
    (ω : ManifoldForm I M k) {x : M} (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    chartForm I e ω =ᶠ[𝓝[range I] (e.extend I x)]
      formPullback (I.extendCoordChange e e') (fderivWithin ℝ (I.extendCoordChange e e') (range I))
        (chartForm I e' ω) := by
  filter_upwards [I.extendCoordChange_source_mem_nhdsWithin' hx hx'] with y hy
  rw [← OpenPartialHomeomorph.extend_image_source_inter] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  exact chartForm_eq_formPullback he he' ω hz.1 hz.2

end ChartChange

/-! #### Regularity -/

section Regularity

variable (I) in
/-- **A `C^r` form**: its expressions in the charts `chartAt H x` of the atlas are `C^r` on the
chart targets. -/
def ContMDiffForm (r : WithTop ℕ∞) (ω : ManifoldForm I M k) : Prop :=
  ∀ x : M, ContDiffOn ℝ r (chartForm I (chartAt H x) ω) (extChartAt I x).target

theorem contMDiffForm_zero_form (r : WithTop ℕ∞) : ContMDiffForm I r (0 : ManifoldForm I M k) :=
  fun x => by rw [chartForm_zero]; exact contDiffOn_const

theorem ContMDiffForm.of_le {r r' : WithTop ℕ∞} {ω : ManifoldForm I M k}
    (hω : ContMDiffForm I r ω) (h : r' ≤ r) : ContMDiffForm I r' ω :=
  fun x => (hω x).of_le h

theorem ContMDiffForm.add {r : WithTop ℕ∞} {ω₁ ω₂ : ManifoldForm I M k}
    (h₁ : ContMDiffForm I r ω₁) (h₂ : ContMDiffForm I r ω₂) : ContMDiffForm I r (ω₁ + ω₂) :=
  fun x => by rw [chartForm_add]; exact (h₁ x).add (h₂ x)

theorem ContMDiffForm.finsetSum {ι : Type*} (u : Finset ι) {r : WithTop ℕ∞}
    {ω : ι → ManifoldForm I M k} (h : ∀ j ∈ u, ContMDiffForm I r (ω j)) :
    ContMDiffForm I r (∑ j ∈ u, ω j) := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using contMDiffForm_zero_form r
  | insert j u hj ih =>
    rw [Finset.sum_insert hj]
    exact (h j (Finset.mem_insert_self j u)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- A `C^r` form is `C^r` within `range I` at the points of a chart target. -/
theorem ContMDiffForm.contDiffWithinAt {r : WithTop ℕ∞} {ω : ManifoldForm I M k}
    (hω : ContMDiffForm I r ω) (x : M) {y : E} (hy : y ∈ (extChartAt I x).target) :
    ContDiffWithinAt ℝ r (chartForm I (chartAt H x) ω) (range I) y :=
  ((hω x) y hy).mono_of_mem_nhdsWithin (extChartAt_target_mem_nhdsWithin_of_mem hy)

/-- A `C¹` form is differentiable within `range I` at the points of a chart target. -/
theorem ContMDiffForm.differentiableWithinAt {r : WithTop ℕ∞} {ω : ManifoldForm I M k}
    (hω : ContMDiffForm I r ω) (hr : 1 ≤ r) (x : M) {y : E} (hy : y ∈ (extChartAt I x).target) :
    DifferentiableWithinAt ℝ (chartForm I (chartAt H x) ω) (range I) y :=
  ((hω.contDiffWithinAt x hy).of_le hr).differentiableWithinAt one_ne_zero

variable [IsManifold I ∞ M]

/-- **The product of a `C^r` function and a `C^r` form is `C^r`.** -/
theorem ContMDiffForm.smulFun {r : WithTop ℕ∞} (hr : r ≤ ∞) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) r f) {ω : ManifoldForm I M k} (hω : ContMDiffForm I r ω) :
    ContMDiffForm I r (ManifoldForm.smulFun f ω) := fun x => by
  have hf' : ContDiffOn ℝ r (f ∘ (extChartAt I x).symm) (extChartAt I x).target :=
    contMDiffOn_iff_contDiffOn.1
      (hf.comp_contMDiffOn ((contMDiffOn_extChartAt_symm (n := ∞) x).of_le hr))
  have : chartForm I (chartAt H x) (ManifoldForm.smulFun f ω) =
      fun y => (f ∘ (extChartAt I x).symm) y • chartForm I (chartAt H x) ω y :=
    funext fun y => chartForm_smulFun _ f ω y
  rw [this]
  exact hf'.smul (hω x)

end Regularity

/-! #### The exterior derivative on `M` -/

section ExtDeriv

omit [ChartedSpace H M] in
/-- `d` within a chart target agrees with `d` within `range I` (the target is relatively open). -/
theorem extDerivWithin_extend_target {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m : ℕ} (η : E → E [⋀^Fin m]→L[ℝ] F) (e : OpenPartialHomeomorph M H) {y : E}
    (hy : y ∈ (e.extend I).target) :
    extDerivWithin η (e.extend I).target y = extDerivWithin η (range I) y := by
  have hU : I.symm ⁻¹' e.target ∈ 𝓝 y := by
    rw [e.extend_target] at hy
    exact (e.open_target.preimage I.continuous_symm).mem_nhds hy.1
  rw [e.extend_target, inter_comm]
  simp only [extDerivWithin, fderivWithin_inter hU]

/-- `d` of a `C¹` form on `ℝⁿ` is continuous on a set with unique derivatives. -/
theorem continuousOn_extDerivWithin {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ}
    {η : E → E [⋀^Fin m]→L[ℝ] F} {s : Set E} (hη : ContDiffOn ℝ 1 η s) (hs : UniqueDiffOn ℝ s) :
    ContinuousOn (extDerivWithin η s) s :=
  (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F).continuous.comp_continuousOn
    (hη.continuousOn_fderivWithin hs le_rfl)

/-- **The exterior derivative of a form on `M`**: `(dω)(x)` is the exterior derivative, within
`range I`, of the expression of `ω` in the chart at `x`, at `x` (Mathlib's `extDerivWithin`).
By `chartForm_extDeriv` it reads the same in every chart of the maximal atlas. -/
def extDeriv (ω : ManifoldForm I M k) : ManifoldForm I M (k + 1) :=
  fun x => (extDerivWithin (chartForm I (chartAt H x) ω) (range I) (extChartAt I x x) :
    E [⋀^Fin (k + 1)]→L[ℝ] ℝ)

theorem extDeriv_apply (ω : ManifoldForm I M k) (x : M) :
    extDeriv ω x = extDerivWithin (chartForm I (chartAt H x) ω) (range I) (extChartAt I x x) :=
  rfl

/-- **`d` is local**: if `ω` vanishes near `x`, then `dω(x) = 0`. -/
theorem extDeriv_eq_zero_of_eventually_eq_zero {ω : ManifoldForm I M k} {x : M}
    (h : ∀ᶠ y in 𝓝 x, ω y = 0) : extDeriv ω x = 0 := by
  have h' : chartForm I (chartAt H x) ω =ᶠ[𝓝[range I] (extChartAt I x x)] 0 := by
    filter_upwards [nhdsWithin_le_nhds (extChartAt_preimage_mem_nhds h)] with y hy
    ext v
    simp only [mem_preimage] at hy
    rw [chartForm_apply, ← extChartAt, hy]
    rfl
  rw [extDeriv_apply, h'.extDerivWithin_eq
    (h'.self_of_nhdsWithin (extChartAt_target_subset_range x (mem_extChartAt_target x))),
    extDerivWithin, fderivWithin_zero]
  exact map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ)

/-- `dω` vanishes outside the closed support of `ω`. -/
theorem extDeriv_eq_zero_of_notMem_tsupport {ω : ManifoldForm I M k} {x : M}
    (hx : x ∉ tsupport ω) : extDeriv ω x = 0 :=
  extDeriv_eq_zero_of_eventually_eq_zero <| by
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
    exact eq_zero_of_notMem_tsupport hy

/-- **The support of `dω` lies in the support of `ω`.** -/
theorem tsupport_extDeriv_subset (ω : ManifoldForm I M k) : tsupport (extDeriv ω) ⊆ tsupport ω :=
  closure_minimal (fun _ hx => by_contra fun h => hx (extDeriv_eq_zero_of_notMem_tsupport h))
    isClosed_closure

/-- **`d` is additive** on differentiable forms. -/
theorem extDeriv_add {ω₁ ω₂ : ManifoldForm I M k} (h₁ : ContMDiffForm I 1 ω₁)
    (h₂ : ContMDiffForm I 1 ω₂) : extDeriv (ω₁ + ω₂) = extDeriv ω₁ + extDeriv ω₂ := by
  funext x
  have hx := mem_extChartAt_target (I := I) x
  rw [Pi.add_apply, extDeriv_apply, extDeriv_apply, extDeriv_apply, chartForm_add]
  exact extDerivWithin_add (I.uniqueDiffOn _ (mem_range_self _))
    (h₁.differentiableWithinAt le_rfl x hx) (h₂.differentiableWithinAt le_rfl x hx)

@[simp]
theorem extDeriv_zero : extDeriv (0 : ManifoldForm I M k) = 0 := by
  funext x
  exact extDeriv_eq_zero_of_eventually_eq_zero (Eventually.of_forall fun _ => rfl)

/-- **`d` commutes with finite sums** of `C¹` forms. -/
theorem extDeriv_finsetSum {ι : Type*} (u : Finset ι) {ω : ι → ManifoldForm I M k}
    (h : ∀ j ∈ u, ContMDiffForm I 1 (ω j)) : extDeriv (∑ j ∈ u, ω j) = ∑ j ∈ u, extDeriv (ω j) := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | insert j u hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      extDeriv_add (h j (Finset.mem_insert_self j u))
        (ContMDiffForm.finsetSum u fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

variable [IsManifold I ∞ M]

/-- **Chart independence of `d`**: in every chart `e` of the maximal atlas, the expression of
`dω` is the exterior derivative (within `range I`) of the expression of `ω`, for a `C¹` form `ω`
on a `C^∞` manifold.  The proof is the naturality of `d` under the chart change
(`extDerivWithin_eq_formPullback`). -/
theorem chartForm_extDeriv {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {ω : ManifoldForm I M k}
    (hω : ContMDiffForm I 1 ω) {x : M} (hx : x ∈ e.source) :
    chartForm I e (extDeriv ω) (e.extend I x) = extDerivWithin (chartForm I e ω) (range I)
      (e.extend I x) := by
  have hc := IsManifold.chart_mem_maximalAtlas (I := I) (n := ∞) x
  have hxc := mem_chart_source H x
  have hfx : I.extendCoordChange e (chartAt H x) (e.extend I x) = extChartAt I x x := by
    simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply]
    rw [e.extend_left_inv hx]; rfl
  have hmaps : MapsTo (I.extendCoordChange e (chartAt H x)) (range I) (range I) := fun y _ => by
    simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply,
      OpenPartialHomeomorph.extend_coe]
    exact mem_range_self _
  have hxI : e.extend I x ∈ range I := by
    rw [OpenPartialHomeomorph.extend_coe]; exact mem_range_self _
  rw [extDerivWithin_eq_formPullback (r := ∞) (chartForm_eventuallyEq_formPullback he hc ω hx hxc)
    (by rw [hfx]; exact hω.differentiableWithinAt le_rfl x (mem_extChartAt_target x))
    (I.contDiffWithinAt_extendCoordChange' he hc hx hxc) (by norm_cast) I.uniqueDiffOn
    (I.range_subset_closure_interior hxI) hxI hmaps, formPullback, hfx]
  ext v
  rw [chartForm_apply, e.extend_left_inv hx]
  rfl

/-- **Chart independence of `d`**, at the points of the chart target. -/
theorem chartForm_extDeriv_of_mem_target {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {ω : ManifoldForm I M k}
    (hω : ContMDiffForm I 1 ω) {y : E} (hy : y ∈ (e.extend I).target) :
    chartForm I e (extDeriv ω) y = extDerivWithin (chartForm I e ω) (e.extend I).target y := by
  have hy' : (e.extend I).symm y ∈ e.source := by
    rw [← e.extend_source (I := I)]; exact (e.extend I).map_target hy
  rw [extDerivWithin_extend_target _ e hy, ← (e.extend I).right_inv hy]
  exact chartForm_extDeriv he hω hy'

/-- **`dω` of a `C¹` form is continuous** (its expressions in the charts are continuous). -/
theorem contMDiffForm_zero_extDeriv {ω : ManifoldForm I M k} (hω : ContMDiffForm I 1 ω) :
    ContMDiffForm I 0 (extDeriv ω) := fun x => by
  refine contDiffOn_zero.2 ((continuousOn_extDerivWithin (hω x)
    (uniqueDiffOn_extChartAt_target x)).congr fun y hy => ?_)
  exact chartForm_extDeriv_of_mem_target (IsManifold.chart_mem_maximalAtlas x) hω hy

end ExtDeriv

end ManifoldForm

end Forms

end Polyfold
