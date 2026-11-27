import GWMemoir.Evaluation
import GWMemoir.Invariants
import Polyfold.Chapter4.ManifoldForms
import Polyfold.Chapter5.Poincare

/-!
Hofer–Wysocki–Zehnder, *Applications of Polyfold Theory I: The Polyfolds of Gromov–Witten
Theory*, Memoirs AMS 248 (2017), **Theorem 1.12** (p. 9), with `ev : Z → Qᵐ` and a de Rham form
on `Qᵐ`, compared with the book (*Polyfold and Fredholm Theory*, Springer 2021): Definition
4.4.1 (sc-differential forms), p. 372 (`Ωᵏ_{ep,∞}`), p. 720 (forms on polyfolds), Theorem
16.6.6.

## The memoir, paraphrased

(Theorem 1.12) `Ψ^Q_{A,g,m}` integrates `γ^*(PD τ) ∧ ev_1^*α_1 ∧ … ∧ ev_m^*α_m` over the
perturbed solution set, for de Rham classes `α_i` on `Q`; the value does not depend on the
admissible perturbation and only on the classes of the forms.

## What is formalized (namespace `GWMemoir`)

* `formFamily τ`: a form `τ` on a manifold `M` (Mathlib tangent spaces, `ManifoldForm`) read on
  the tangent spaces of `manifoldMPolyfold`, through `T_xX ≅ F` of the chart `chartAt H (h x)`.
* `chartForm_formFamily`: in the manifold chart of `e`, the chart form of `formFamily τ` is the
  chart expression `τ_e` (`tangentChartMap_ofVec_manifoldChart`: the tangent map of a chart change
  is the derivative of `I.extendCoordChange`).
* `formFamily_mem_scForms`: for `C^∞` `τ`, `formFamily τ` is an sc-differential form;
  `formFamily_mem_epForms` on the trivial ep-groupoid; **`toScForm`**: `τ` as an element of
  `Ωᵏ_sc(M)` on the polyfold `manifoldClass`.
* **`extD_formFamily_eq_zero`**: for a closed `C^∞` form `τ`, the sc-exterior derivative of
  `formFamily τ` vanishes (the chart formula of `d` for the constant scale,
  `chartD_formFamily_eq_zero`); `d_toScForm_eq_zero`: then `d(toScForm τ) = 0`.
* **`memoir_theorem_1_12_manifold`**: `memoir_theorem_1_12` for `ev = gwEv : Z → Qᵐ` and
  `toScForm τ` with `τ` a closed `C^∞` form on `Qᵐ`, from `Evaluation_ScSmooth`.

## Readings

* The memoir's `ev_1^*α_1 ∧ … ∧ ev_m^*α_m` is `ev^*(pr_1^*α_1 ∧ … ∧ pr_m^*α_m)` for one form on
  `Qᵐ`; here `τ` is any closed form on `Qᵐ`.  The factor `γ^*(PD τ)` with `γ : Z → M_{g,m}`
  (Theorem 1.8) is not included: `M_{g,m}` is an orbifold, not a manifold of Mathlib.
* The chart formula of `d` (2021 p. 197) for the constant sc-structure: in the chart of `e`, the
  chart form of `d(formFamily τ)` is `Σ_j (-1)^j D(τ_e · (v₀, …, v̂_j, …, v_k))(a)(v_j)`, which is
  `(dτ)_e(a)(v)`; on the constant scale `scDeriv` is the derivative `fderiv`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter
open scoped Manifold ContDiff

noncomputable section

namespace GWMemoir

open Polyfold

universe u

/-! ### Relatively open sets: tangent sets and Whitney sums -/

section RelOpen

variable {E : ScBanach} {C S : Set (E 0)}

/-- On a relatively open subset `S` of a partial quadrant (`r = id`), `TS = S¹ × E₀`. -/
theorem retractTangent_of_isRelOpen (hS : IsRelOpenInQuadrant E C S) :
    retractTangent E C S = E.tangentSet S := by
  have h := retractTangent_eq (ScRetraction.id hS)
  have hret : (ScRetraction.id hS).retract = S := image_id S
  rw [hret] at h
  rw [h, ScRetraction.tangent]
  change Polyfold.tangentMap S _root_.id '' E.tangentSet S = _
  rw [(tangentMap_id_eqOn hS.isScDomain).image_eq, image_id]

/-- On a relatively open `S`, `⊕ₖ TS = S¹ × E₀ᵏ`. -/
theorem retractWhitney_of_isRelOpen (hS : IsRelOpenInQuadrant E C S) (k : ℕ) :
    retractWhitney E C S k = E.whitneySet k S := by
  ext q
  rw [ScBanach.mem_whitneySet]
  refine ⟨fun hq => hq.1, fun hq => ⟨hq, fun i => ?_⟩⟩
  rw [retractTangent_of_isRelOpen hS]
  exact hq

end RelOpen

/-- A form whose chart form is `C^∞` on `O¹ × E₀ᵏ`, for a chart whose model set `O` is relatively
open, is sc-smooth in that chart. -/
theorem isChartScSmooth_of_contDiffOn {X : Type u} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] {P : MPolyfold X}
    {φ : MChart X} (hφ : P.IsChart φ) {k : ℕ}
    {σ : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ}
    (hO : IsRelOpenInQuadrant φ.model.E φ.model.C φ.model.O)
    (hσ : ContDiffOn ℝ ∞ (MPolyfold.chartForm hφ σ) (φ.model.E.whitneySet k φ.model.O)) :
    MPolyfold.IsChartScSmooth hφ σ := by
  have hW := hO.whitneySet k
  have hR := retractWhitney_of_isRelOpen hO k
  exact (isScSmoothRetractMap_iff_exists (hR ▸ hW.isScRetract)).2
    ⟨mapsTo_univ _ _, ScRetraction.id hW, (image_id _).trans hR.symm,
      IsScSmooth.of_contDiffOn_finiteDimensional (V := ℝ) hW.isScDomain hσ⟩

/-! ### Forms on a manifold as sc-forms on its M-polyfold -/

section Forms

open MPolyfold

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (h : X ≃ₜ M) {k : ℕ}

omit [FiniteDimensional ℝ F] in
lemma const_toBase_eq (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (m : ℕ) : (ScBanach.const V).toBase m = ContinuousLinearMap.id ℝ V :=
  ContinuousLinearMap.ext (ScBanach.const_toBase V m)

omit [IsManifold I ∞ M] in
/-- The model set of a manifold chart is open in `F`. -/
lemma isRelOpen_manifoldChart (e : OpenPartialHomeomorph M H) :
    IsRelOpenInQuadrant (manifoldChart I h e).model.E (manifoldChart I h e).model.C
      (manifoldChart I h e).model.O :=
  ⟨isPartialQuadrant_univ _, _, e.isOpen_extend_target (I := I), (inter_univ _).symm⟩

omit [IsManifold I ∞ M] in
lemma isRelOpen_manifoldChart_overlap (e e' : OpenPartialHomeomorph M H) :
    IsRelOpenInQuadrant (manifoldChart I h e).model.E (manifoldChart I h e).model.C
      ((manifoldChart I h e).overlap (manifoldChart I h e')) :=
  ⟨isPartialQuadrant_univ _, _, isOpen_manifoldChart_overlap (I := I) h e e', (inter_univ _).symm⟩

/-- **The tangent map of a chart change of `M`** (formula (5) of Definition 2.3.14 for the
manifold charts): `Tψ ∘ (Tφ)⁻¹ (a, v) = (·, D(ψ ∘ φ⁻¹)(a) v)`. -/
theorem tangentChartMap_ofVec_manifoldChart {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) (he' : e' ∈ IsManifold.maximalAtlas I ∞ M)
    (hφ : (manifoldMPolyfold I M h).IsChart (manifoldChart I h e))
    (hψ : (manifoldMPolyfold I M h).IsChart (manifoldChart I h e'))
    {a : (manifoldChart I h e).model.E.tangent 0}
    (ha : a ∈ retractTangent (manifoldChart I h e).model.E (manifoldChart I h e).model.C
      (manifoldChart I h e).model.O)
    (hov : (a.1 : F) ∈ (manifoldChart I h e).overlap (manifoldChart I h e')) :
    ((tangentChartMap hψ (TangentSpace.mk (TangentPre.ofVec hφ ha))).2 : F) =
      fderiv ℝ (I.extendCoordChange e e') a.1 a.2 := by
  have hrel := isRelOpen_manifoldChart_overlap (I := I) h e e'
  have ha2 : a ∈ retractTangent (manifoldChart I h e).model.E (manifoldChart I h e).model.C
      ((manifoldChart I h e).overlap (manifoldChart I h e')) := by
    rw [retractTangent_of_isRelOpen hrel]
    change (ScBanach.const F).toBase 1 a.1 ∈ (manifoldChart I h e).overlap (manifoldChart I h e')
    have e0 : (ScBanach.const F).toBase 1 a.1 = (a.1 : F) := ScBanach.const_toBase F 1 a.1
    exact e0 ▸ hov
  rw [tangentChartMap_mk_ofVec_of_mem hφ hψ ha ha2]
  have hf := (manifoldChart_compatible h he he').1
  rw [retractTangentMap_apply hf (ScRetraction.id hrel) (image_id _) ha2]
  have hsm := hf.comp_isScSmooth (ScRetraction.id hrel) (image_id _)
  have hS := isOpen_manifoldChart_overlap (I := I) h e e'
  set y : F := a.1 with hy
  have hcd : ContDiffAt ℝ ∞ (I.extendCoordChange e e') y :=
    ((I.contDiffOn_extendCoordChange he he').mono
      (manifoldChart_overlap_subset (I := I) h e e')).contDiffAt (hS.mem_nhds hov)
  have hD : HasFDerivWithinAt (I.extendCoordChange e e') (fderiv ℝ (I.extendCoordChange e e') y)
      ((manifoldChart I h e).overlap (manifoldChart I h e')) y :=
    ((hcd.differentiableAt (by simp)).hasFDerivAt).hasFDerivWithinAt
  have e1 : (manifoldChart I h e).model.E.toBase 1 = ContinuousLinearMap.id ℝ F :=
    const_toBase_eq F 1
  have e2 : (manifoldChart I h e).model.E.lvlSet (ScRetraction.id hrel).U 1 =
      (manifoldChart I h e).overlap (manifoldChart I h e') := ScBanach.lvlSet_const _ _
  have hx : a.1 ∈ (manifoldChart I h e).model.E.lvlSet (ScRetraction.id hrel).U 1 := by
    rw [e2]; exact hov
  have hU : UniqueDiffWithinAt ℝ
      ((manifoldChart I h e).model.E.lvlSet (ScRetraction.id hrel).U 1) a.1 := by
    rw [e2]
    have := hS.uniqueDiffWithinAt (𝕜 := ℝ) (show y ∈ (manifoldChart I h e).overlap
      (manifoldChart I h e') from hov)
    exact this
  rw [hsm.isSc1.scDeriv_eq_of_hasFDerivWithinAt hx hU (L := fderiv ℝ (I.extendCoordChange e e') y)
    (by
      rw [e1, e2]
      convert hD using 1
      rw [← manifoldChart_transition (I := I) h e e']; rfl)]
  rfl

/-- The chart `chartAt H (h x)` of the M-polyfold at a point `x` of `X¹`. -/
abbrev baseChart (x : (manifoldMPolyfold I M h).Level 1) : MChart X :=
  manifoldChart I h (chartAt H (h ((manifoldMPolyfold I M h).levelVal 1 x)))

lemma isChart_baseChart (x : (manifoldMPolyfold I M h).Level 1) :
    (manifoldMPolyfold I M h).IsChart (baseChart h x) :=
  isChart_manifoldChart_chartAt h _

lemma mem_baseChart_source (x : (manifoldMPolyfold I M h).Level 1) :
    (manifoldMPolyfold I M h).levelVal 1 x ∈ (baseChart h x).source :=
  mem_manifoldChart_chartAt_source h _

/-- **A form on `M` as a family of forms on the tangent spaces of the M-polyfold**: at `x`,
`τ(h x)` read through the linear isomorphism `T_xX ≅ F` of the chart `chartAt H (h x)` (in which
Mathlib expresses `T_{h x}M = F`). -/
def formFamily (τ : ManifoldForm I M k) : ∀ x : (manifoldMPolyfold I M h).Level 1,
    (manifoldMPolyfold I M h).tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ := fun x =>
  (τ (h ((manifoldMPolyfold I M h).levelVal 1 x))).toAlternatingMap.compLinearMap
    ((tangentFiberModel (isChart_baseChart h x) (mem_baseChart_source h x)).subtype ∘ₗ
      (tangentFiberLinearEquiv (isChart_baseChart h x) (mem_baseChart_source h x)).toLinearMap)

lemma formFamily_apply (τ : ManifoldForm I M k) (x : (manifoldMPolyfold I M h).Level 1)
    (α : Fin k → (manifoldMPolyfold I M h).tangentFiber x) :
    formFamily h τ x α = τ (h ((manifoldMPolyfold I M h).levelVal 1 x))
      (fun i => (tangentChartMap (isChart_baseChart h x) (α i).1).2) := rfl

/-- **The chart form of `formFamily τ` is the chart expression of `τ`**: in the manifold chart
of `e`, `(formFamily τ)_φ(a, v₁, …, v_k) = τ_e(a)(v₁, …, v_k)` on `⊕ₖ TO = O × Fᵏ`. -/
theorem chartForm_formFamily (τ : ManifoldForm I M k) {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {q : ((manifoldChart I h e).model.E.whitney k) 0}
    (hq : q ∈ retractWhitney (manifoldChart I h e).model.E (manifoldChart I h e).model.C
      (manifoldChart I h e).model.O k) :
    chartForm (isChart_manifoldChart h he) (formFamily h τ) q =
      ManifoldForm.chartForm I e τ q.1 (ScBanach.whitneyVec q) := by
  have hφ := isChart_manifoldChart h he
  have hq1 : ((manifoldChart I h e).model.E.toBase 1 q.1 : F) = q.1 :=
    ScBanach.const_toBase F 1 q.1
  have hmem : (q.1 : F) ∈ (e.extend I).target := hq1 ▸ hq.1
  set y : M := (e.extend I).symm q.1 with hydef
  set x := chartPoint hφ hq.1 with hx
  have hy : h ((manifoldMPolyfold I M h).levelVal 1 x) = y := by
    rw [hx, levelVal_chartPoint]
    change h (h.symm ((e.extend I).symm _)) = _
    rw [h.apply_symm_apply, hq1]
  have hys : y ∈ e.source := by
    rw [← e.extend_source (I := I)]; exact (e.extend I).map_target hmem
  have hov : (q.1 : F) ∈ (manifoldChart I h e).overlap (baseChart h x) := by
    refine ⟨h.symm y, ⟨?_, ?_⟩, ?_⟩
    · change h (h.symm y) ∈ e.source; rw [h.apply_symm_apply]; exact hys
    · change h (h.symm y) ∈ (chartAt H (h ((manifoldMPolyfold I M h).levelVal 1 x))).source
      rw [h.apply_symm_apply, hy]; exact mem_chart_source H y
    · change e.extend I (h (h.symm y)) = q.1
      rw [h.apply_symm_apply]; exact (e.extend I).right_inv hmem
  have hcm := IsManifold.chart_mem_maximalAtlas (I := I) (n := ∞)
    (h ((manifoldMPolyfold I M h).levelVal 1 x))
  have key : ∀ p : M, p = y → τ p (fun i => fderiv ℝ (I.extendCoordChange e (chartAt H p)) q.1
      (ScBanach.whitneyVec q i)) = ManifoldForm.chartForm I e τ q.1 (ScBanach.whitneyVec q) := by
    rintro _ rfl
    have hey : e.extend I y = q.1 := by rw [hydef]; exact (e.extend I).right_inv hmem
    refine congrArg (τ y) (funext fun i => ?_)
    show _ = fderivWithin ℝ (I.extendCoordChange e (chartAt H y)) (range I) (e.extend I y) _
    rw [I.range_eq_univ, fderivWithin_univ, hey]
  rw [MPolyfold.chartForm, dif_pos hq, formFamily_apply]
  refine Eq.trans (congrArg (τ (h ((manifoldMPolyfold I M h).levelVal 1 x)))
    (funext fun i => tangentChartMap_ofVec_manifoldChart h he hcm hφ (isChart_baseChart h x)
      (hq.2 i) hov)) ?_
  exact key _ hy

omit [IsManifold I ∞ M] [T2Space X] [ParacompactSpace X] in
/-- Evaluation of a `C^∞` family of alternating forms on `C^∞` vectors is `C^∞` (finite
dimensions: expand in a basis). -/
theorem contDiffOn_alt_eval {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] {s : Set D}
    {A : D → F [⋀^Fin k]→L[ℝ] ℝ} {v : D → Fin k → F} (hA : ContDiffOn ℝ ∞ A s)
    (hv : ∀ i, ContDiff ℝ ∞ fun d => v d i) : ContDiffOn ℝ ∞ (fun d => A d (v d)) s := by
  classical
  set b := Module.finBasis ℝ F
  have hsum : (fun d => A d (v d)) = fun d => ∑ r : Fin k → Fin (Module.finrank ℝ F),
      (∏ i, b.repr (v d i) (r i)) * A d (fun i => b (r i)) :=
    funext fun d => multilinear_eq_sum_basis b (A d).toMultilinearMap (v d)
  rw [hsum]
  refine ContDiffOn.sum fun r _ => (contDiffOn_prod fun i _ => ?_).mul ?_
  · exact ((LinearMap.toContinuousLinearMap (b.coord (r i))).contDiff.comp (hv i)).contDiffOn
  · exact (ContinuousAlternatingMap.apply ℝ F ℝ (fun i => b (r i))).contDiff.comp_contDiffOn hA

/-- **In the chart `chartAt H x₀`, the chart form of `formFamily τ` is `C^∞`** on `O × Fᵏ`, for
a `C^∞` form `τ`. -/
theorem contDiffOn_chartForm_formFamily {τ : ManifoldForm I M k}
    (hτ : ManifoldForm.ContMDiffForm I ∞ τ) (x₀ : M) :
    ContDiffOn ℝ ∞ (chartForm (isChart_manifoldChart h (IsManifold.chart_mem_maximalAtlas x₀))
      (formFamily h τ))
      ((manifoldChart I h (chartAt H x₀)).model.E.whitneySet k
        (manifoldChart I h (chartAt H x₀)).model.O) := by
  have hO := isRelOpen_manifoldChart (I := I) h (chartAt H x₀)
  have hfst : MapsTo (fun q : ((manifoldChart I h (chartAt H x₀)).model.E.whitney k) 0 =>
      (q.1 : F)) ((manifoldChart I h (chartAt H x₀)).model.E.whitneySet k
        (manifoldChart I h (chartAt H x₀)).model.O) (extChartAt I x₀).target := fun q hq => by
    have h1 := ScBanach.mem_whitneySet.1 hq
    have hq1 : ((manifoldChart I h (chartAt H x₀)).model.E.toBase 1 q.1 : F) = q.1 :=
      ScBanach.const_toBase F 1 q.1
    show (q.1 : F) ∈ _
    exact hq1 ▸ h1
  have hA : ContDiffOn ℝ ∞ (fun q : ((manifoldChart I h (chartAt H x₀)).model.E.whitney k) 0 =>
      ManifoldForm.chartForm I (chartAt H x₀) τ (q.1 : F))
      ((manifoldChart I h (chartAt H x₀)).model.E.whitneySet k
        (manifoldChart I h (chartAt H x₀)).model.O) :=
    (hτ x₀).comp contDiff_fst.contDiffOn hfst
  have hv : ∀ i, ContDiff ℝ ∞ fun q : ((manifoldChart I h (chartAt H x₀)).model.E.whitney k) 0 =>
      (ScBanach.whitneyVec q i : F) := fun i =>
    (contDiff_apply ℝ F i).comp
      (((manifoldChart I h (chartAt H x₀)).model.E.fiberVecL 0 k).contDiff.comp contDiff_snd)
  refine (contDiffOn_alt_eval hA hv).congr fun q hq => ?_
  exact chartForm_formFamily h τ (IsManifold.chart_mem_maximalAtlas x₀)
    ((retractWhitney_of_isRelOpen hO k).symm ▸ hq)

/-- **A `C^∞` form on `M` is an sc-differential form on its M-polyfold** (2021 Definition 4.4.1):
its chart forms in the charts `chartAt H x` cover `X¹` and are `C^∞`, hence sc-smooth. -/
theorem formFamily_mem_scForms {τ : ManifoldForm I M k} (hτ : ManifoldForm.ContMDiffForm I ∞ τ) :
    formFamily h τ ∈ (manifoldMPolyfold I M h).scForms k := by
  refine isScForm_of_cover _ fun x => ⟨_, isChart_baseChart h x, mem_baseChart_source h x, ?_⟩
  exact isChartScSmooth_of_contDiffOn _ (isRelOpen_manifoldChart (I := I) h _)
    (contDiffOn_chartForm_formFamily h hτ _)

/-- The same on the trivial ep-groupoid: compatibility with the morphisms (identities) is
automatic. -/
theorem formFamily_mem_epForms {τ : ManifoldForm I M k} (hτ : ManifoldForm.ContMDiffForm I ∞ τ) :
    formFamily h τ ∈ (EpGroupoid.trivial (manifoldMPolyfold I M h)).epForms k :=
  ⟨formFamily_mem_scForms h hτ, (EpGroupoid.isMorCompatible_iff_formPullback _).2 rfl⟩

variable (I M) in
/-- **A `C^∞` form `τ` on `M` as an sc-differential form on the polyfold `M`** (2021 p. 720):
the class of `(formFamily τ, manifoldStructure)` in `Ω^k_sc(M)`. -/
def toScForm (τ : ManifoldForm I M k) (hτ : ManifoldForm.ContMDiffForm I ∞ τ) :
    PolyfoldClass.ScForm (manifoldClass I M h) k :=
  PolyfoldClass.ScForm.mk (manifoldStructure I M h) rfl
    ((manifoldStructure I M h).X.epFormsInftyOf k 0 ⟨formFamily h τ, formFamily_mem_epForms h hτ⟩)

/-- The model space `F` (constant scale), the model set and the quadrant of the chart
`chartAt H x₀`. -/
local notation "𝔼[" x "]" => LocalModel.E (MChart.model (manifoldChart I h (chartAt H x)))
local notation "𝕆[" x "]" => LocalModel.O (MChart.model (manifoldChart I h (chartAt H x)))
local notation "ℂ[" x "]" => LocalModel.C (MChart.model (manifoldChart I h (chartAt H x)))

/-- **One term of the chart formula of `d` for the constant scale**: in the chart `chartAt H x₀`,
the sc-derivative of the chart form of `formFamily τ` in a direction `(b, 0)` is the derivative of
`y ↦ τ_e(y)(w)` in the direction `b` (finite dimensions: `scDeriv` is `fderiv`,
`IsSc1.hasFDerivWithinAt_of_finiteDimensional`; on the open set `O × Fᵏ` the chart form is
`τ_e(y)(w)`, `chartForm_formFamily`). -/
theorem scDeriv_chartForm_formFamily {τ : ManifoldForm I M k}
    (hτ : ManifoldForm.ContMDiffForm I ∞ τ) (x₀ : M)
    {p : (𝔼[x₀].whitney k) 1}
    (hp : (𝔼[x₀].whitney k).toBase 1 p ∈
      𝔼[x₀].whitneySet k
        𝕆[x₀])
    (b : F) :
    scDeriv (F := ScBanach.const ℝ) (𝔼[x₀].whitneySet k
        𝕆[x₀])
      (chartForm (isChart_manifoldChart h (IsManifold.chart_mem_maximalAtlas x₀))
        (formFamily h τ)) p (ScBanach.whitneyMk (E := 𝔼[x₀]) b 0) =
    fderiv ℝ (fun y : F => ManifoldForm.chartForm I (chartAt H x₀) τ y
        (ScBanach.whitneyVec ((𝔼[x₀].whitney k).toBase 1 p)))
      ((𝔼[x₀].whitney k).toBase 1 p).1 b := by
  have hφ := isChart_manifoldChart h (IsManifold.chart_mem_maximalAtlas (I := I) (n := ∞) x₀)
  have hO := isRelOpen_manifoldChart (I := I) h (chartAt H x₀)
  have : FiniteDimensional ℝ ((𝔼[x₀].whitney k) 0) :=
    finiteDimensional_whitney (ScBanach.const F) k
  have hω := (mem_scForms.1 (formFamily_mem_scForms h hτ)).isRetractScForm hφ
  have hΩ := (hω.isAmbientScForm_relOpen hO).isScSmooth.isSc1
  set z := (𝔼[x₀].whitney k).toBase 1 p with hz
  have hT : IsOpen ((chartAt H x₀).extend I).target := (chartAt H x₀).isOpen_extend_target
  have hU : IsOpen (𝔼[x₀].whitneySet k
      𝕆[x₀]) := by
    change IsOpen ((ScBanach.const F).lvlSet ((chartAt H x₀).extend I).target 1 ×ˢ univ)
    rw [ScBanach.lvlSet_const]
    exact hT.prod isOpen_univ
  have hz1 : (z.1 : F) ∈ ((chartAt H x₀).extend I).target := by
    have h1 := ScBanach.mem_whitneySet.1 hp
    have hq1 : (𝔼[x₀].toBase 1 z.1 : F) = z.1 :=
      ScBanach.const_toBase F 1 z.1
    exact hq1 ▸ h1
  have hD := (hΩ.hasFDerivWithinAt_of_finiteDimensional hp).hasFDerivAt (hU.mem_nhds hp)
  have hι : HasFDerivAt (fun y : F =>
      (((y : F), z.2) : (𝔼[x₀].whitney k) 0))
      ((ContinuousLinearMap.id ℝ F).prod 0) (z.1 : F) :=
    (hasFDerivAt_id _).prodMk (hasFDerivAt_const _ _)
  have hcomp := hD.comp (z.1 : F) hι
  have heq : (fun y : F => ManifoldForm.chartForm I (chartAt H x₀) τ y (ScBanach.whitneyVec z))
      =ᶠ[𝓝 (z.1 : F)] (chartForm hφ (formFamily h τ)) ∘ fun y : F =>
        (((y : F), z.2) : (𝔼[x₀].whitney k) 0) := by
    filter_upwards [hT.mem_nhds hz1] with y hy
    have hq : (((y : F), z.2) : (𝔼[x₀].whitney k) 0) ∈
        retractWhitney 𝔼[x₀]
          ℂ[x₀] 𝕆[x₀] k := by
      rw [retractWhitney_of_isRelOpen hO]
      refine ScBanach.mem_whitneySet.2 ?_
      have hq1 : (𝔼[x₀].toBase 1 y : F) = y :=
        ScBanach.const_toBase F 1 y
      change 𝔼[x₀].toBase 1 y ∈ _
      rw [hq1]; exact hy
    exact (chartForm_formFamily h τ (IsManifold.chart_mem_maximalAtlas x₀) hq).symm
  have hf := (hcomp.congr_of_eventuallyEq heq).fderiv
  erw [hf]
  simp [ScBanach.whitneyMk]
  rfl

/-- **The chart formula of `d` for a closed form** (2021 p. 197 for the constant scale): in the
chart `chartAt H x₀`, the local exterior derivative of the chart form of `formFamily τ` is
`Σ_j (-1)^j D(τ_e · (v₀, …, v̂_j, …, v_k))(a)(v_j) = (dτ)_e(a)(v)` (`retractD_eq_ambientD`,
`ambientD_apply`, `extDeriv_apply`, `ManifoldForm.chartForm_extDeriv`), which vanishes for
`dτ = 0`. -/
theorem chartD_formFamily_eq_zero {τ : ManifoldForm I M k}
    (hτ : ManifoldForm.ContMDiffForm I ∞ τ) (hd : ManifoldForm.extDeriv τ = 0) (x₀ : M)
    {q : (𝔼[x₀].shift.whitney (k + 1)) 0}
    (hq : q.1 ∈ 𝔼[x₀].shift.lvlSet (𝔼[x₀].lvlSet 𝕆[x₀] 1) 1) :
    chartD (isChart_manifoldChart h (IsManifold.chart_mem_maximalAtlas x₀)) (formFamily h τ) q =
      0 := by
  have hφ := isChart_manifoldChart h (IsManifold.chart_mem_maximalAtlas (I := I) (n := ∞) x₀)
  have hO := isRelOpen_manifoldChart (I := I) h (chartAt H x₀)
  have hω := (mem_scForms.1 (formFamily_mem_scForms h hτ)).isRetractScForm hφ
  unfold chartD
  rw [retractD_eq_ambientD hO (chartRetraction _) (chartRetraction_retract _) hω
    (ScBanach.mem_whitneySet.2 hq), ambientD_apply]
  have hb1 : ∀ y : 𝔼[x₀] 1, 𝔼[x₀].toBase 1 y = (y : F) := fun y => ScBanach.const_toBase F 1 y
  have ha0 : (𝔼[x₀].shift.toBase 1 q.1 : F) ∈ ((chartAt H x₀).extend I).target := by
    have h1 : 𝔼[x₀].toBase 1 (𝔼[x₀].shift.toBase 1 q.1) ∈ ((chartAt H x₀).extend I).target := hq
    rwa [hb1] at h1
  have hterm : ∀ j : Fin (k + 1),
      scDeriv (F := ScBanach.const ℝ) (𝔼[x₀].whitneySet k 𝕆[x₀])
        (chartForm hφ (formFamily h τ))
        (q.1, 𝔼[x₀].fiberPackL 1 k (j.removeNth (ScBanach.whitneyVec q)))
        (ScBanach.whitneyMk (ScBanach.whitneyVec q j) 0) =
      fderiv ℝ (fun y : F => ManifoldForm.chartForm I (chartAt H x₀) τ y
          (j.removeNth fun i => (ScBanach.whitneyVec q i : F)))
        (𝔼[x₀].shift.toBase 1 q.1 : F) (ScBanach.whitneyVec q j : F) := by
    intro j
    have hz : (𝔼[x₀].whitney k).toBase 1
        (q.1, 𝔼[x₀].fiberPackL 1 k (j.removeNth (ScBanach.whitneyVec q))) =
        ((𝔼[x₀].shift.toBase 1 q.1, (𝔼[x₀].fiberPow k).toBase 1
          (𝔼[x₀].fiberPackL 1 k (j.removeNth (ScBanach.whitneyVec q)))) : (𝔼[x₀].whitney k) 0) :=
      ScBanach.prod_toBase _ _ 1 _
    have hvec : ScBanach.whitneyVec ((𝔼[x₀].whitney k).toBase 1
        (q.1, 𝔼[x₀].fiberPackL 1 k (j.removeNth (ScBanach.whitneyVec q)))) =
        j.removeNth fun i => (ScBanach.whitneyVec q i : F) := by
      funext i
      rw [hz]
      change 𝔼[x₀].fiberVecL 0 k ((𝔼[x₀].fiberPow k).toBase 1
        (𝔼[x₀].fiberPackL 1 k (j.removeNth (ScBanach.whitneyVec q)))) i = _
      rw [ScBanach.fiberVecL_toBase, hb1, ScBanach.fiberVecL_fiberPackL]
    have hp : (𝔼[x₀].whitney k).toBase 1
        (q.1, 𝔼[x₀].fiberPackL 1 k (j.removeNth (ScBanach.whitneyVec q))) ∈
          𝔼[x₀].whitneySet k 𝕆[x₀] := by
      rw [hz]
      exact ScBanach.mem_whitneySet.2 hq
    rw [scDeriv_chartForm_formFamily h hτ x₀ hp (ScBanach.whitneyVec q j), hvec, hz]
  rw [Finset.sum_congr rfl fun j _ => by rw [hterm j]]
  have hdiff : DifferentiableAt ℝ (ManifoldForm.chartForm I (chartAt H x₀) τ)
      (𝔼[x₀].shift.toBase 1 q.1 : F) :=
    ((hτ x₀).differentiableOn (by simp) _ ha0).differentiableAt
      ((chartAt H x₀).isOpen_extend_target.mem_nhds ha0)
  have h0 := extDeriv_apply hdiff (fun i => (ScBanach.whitneyVec q i : F))
  have hz0 : extDeriv (ManifoldForm.chartForm I (chartAt H x₀) τ) (𝔼[x₀].shift.toBase 1 q.1 : F) =
      0 := by
    have hsrc : ((chartAt H x₀).extend I).symm (𝔼[x₀].shift.toBase 1 q.1 : F) ∈
        (chartAt H x₀).source := by
      rw [← (chartAt H x₀).extend_source (I := I)]
      exact ((chartAt H x₀).extend I).map_target ha0
    have := ManifoldForm.chartForm_extDeriv (IsManifold.chart_mem_maximalAtlas x₀)
      (hτ.of_le (by simp)) hsrc
    rw [((chartAt H x₀).extend I).right_inv ha0, hd, ManifoldForm.chartForm_zero,
      I.range_eq_univ, extDerivWithin_univ] at this
    exact this.symm
  rw [hz0] at h0
  have h0' : (0 : ℝ) = _ := h0
  refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h0'.symm
  rw [zsmul_eq_mul]
  push_cast
  rfl

/-- **Closed forms go to closed sc-forms** (2021 p. 197, p. 373): for a closed `C^∞` form `τ` on
`M`, the sc-exterior derivative of `formFamily τ` vanishes (`extD_apply` in the chart
`chartAt H x` at each point, `chartD_formFamily_eq_zero`). -/
theorem extD_formFamily_eq_zero {τ : ManifoldForm I M k}
    (hτ : ManifoldForm.ContMDiffForm I ∞ τ) (hd : ManifoldForm.extDeriv τ = 0) :
    extD (formFamily h τ) = 0 := by
  have hsc := mem_scForms.1 (formFamily_mem_scForms h hτ)
  funext x
  refine AlternatingMap.ext fun α => ?_
  change extD (formFamily h τ) x α = 0
  have hφ := isChart_manifoldChart h (IsManifold.chart_mem_maximalAtlas (I := I) (n := ∞)
    (h ((manifoldMPolyfold I M h).levelVal 1 ((manifoldMPolyfold I M h).shift.levelVal 1 x))))
  have hx : (manifoldMPolyfold I M h).shift.levelVal 1 x ∈
      (levelChart hφ ((manifoldMPolyfold I M h).shift.levelVal 1 x)).source :=
    mem_chart_source H _
  rw [extD_apply hφ hsc _ hx α]
  exact chartD_formFamily_eq_zero h hτ hd _
    (levelLift_mem_lvlSet_one ((manifoldMPolyfold I M h).shift_isChart hφ _) hx)

/-- `d[(formFamily τ, manifoldStructure)] = [(d formFamily τ, manifoldStructure)]` vanishes when
`d(formFamily τ) = 0` (2021 p. 373). -/
theorem d_toScForm_eq_zero {τ : ManifoldForm I M k} (hτ : ManifoldForm.ContMDiffForm I ∞ τ)
    (hd : extD (formFamily h τ) = 0) :
    PolyfoldClass.ScForm.d (toScForm I M h τ hτ) = 0 := by
  refine (PolyfoldClass.ScForm.d_mk (manifoldStructure I M h) rfl _).trans ?_
  rw [EP.epFormsInftyD_of]
  have h0 : (manifoldStructure I M h).X.epFormsD k 0
      ⟨formFamily h τ, formFamily_mem_epForms h hτ⟩ = 0 := Subtype.ext hd
  rw [h0, map_zero]
  exact map_zero (PolyfoldClass.ScForm.equivStructureₗ (manifoldStructure I M h) rfl).symm

end Forms

/-! ### Memoir Theorem 1.12 with `ev : Z → Qᵐ` and a closed form on `Qᵐ` -/

section GW

open Polyfold.StrongPolyfoldBundle Polyfold.PolyfoldClass Polyfold.SBLocalization
  GroupoidalCategory GroupoidalCategory.BasicConstruction
  GCT.VectorBundle.StrongPolyfoldBundleConstruction

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
  [T2Space Q] [CompactSpace Q]
  {om : SymplecticForm E Q} {m k : ℕ} {δ : ℝ} {J : AlmostComplexStructure E Q} {k' : ℕ} {δ' : ℝ}

variable {C : GroupoidalCategory.{1}} {U : C.UniformizerConstruction} {CS : CSPred U}
  {h310 : U.HasClassUniformizers} {H : Theorem_3_13 U CS} {hCS : CSClosed U CS}
  {hPF : PointFinite U}
  {h322 : Theorem_3_22 U (gwTransitionData H hCS hPF)}
  {h16 : Theorem_1_6_sc U (gwTransitionData H hCS hPF) h310}
  {hTF : ∀ (α : C.Obj), ∀ Ψ ∈ U.F α, ∀ y : Ψ.P.SmoothLevel, IsTangentFaithfulAt Ψ y}
  {hLF : ∀ (α : C.Obj), ∀ Ψ ∈ U.F α, IsLocallyFaithful Ψ}
  {V : (gwGCT h310 H hCS hPF h322 h16).VectorBundle}
  {Fb : V.StrongBundleUniformizerConstruction (gwPolyfoldConstruction h310 H hCS hPF h322 h16)}
  {h339 : Proposition_3_39 Fb} {L : StableMapLabel om m k δ C}
  {ιV : FibreRepresentation om m k δ L V.toBanachFunctor J k' δ'} {hd : DbarInDom ιV}
  {c : (ofProposition_3_39 Fb h339).BundleCoveringFamily}

/-- **Memoir Theorem 1.12 with the evaluation into `Qᵐ`** (p. 9; 2021 Theorem 16.6.6): with the
hypotheses of `memoir_theorem_1_12`, the named sc-smoothness of `ev = (ev₁, …, ev_m) : Z → Qᵐ`
(`Evaluation_ScSmooth`): admissible perturbations of
`∂̄_J` exist, and for every closed `C^∞` form `τ` on `Qᵐ` (in chart form) and every `η`,
`∫_{S(∂̄_J, P₀)} ev^*(τ + dη) = ∫_{S(∂̄_J, P₁)} ev^*τ`. -/
theorem memoir_theorem_1_12_manifold (h : CRProps Fb h339 ιV hd c)
    (hbump : (gwBundle hTF hLF Fb h339 c).polyfold.AdmitsBumpFunctions)
    (hbd : (gwBundle hTF hLF Fb h339 c).polyfold.boundary = ∅)
    (hcs : GromovCompactness hTF hLF Fb h339 ιV hd c h)
    {m' : ℕ} (o : OrientationRep (dbarSection hTF hLF Fb h339 ιV hd c h))
    (ho : o.a = sectionRepOfFunctor (gwStructure hTF hLF Fb h339 c) rfl _
      (dbarFunctor_mem_fredholm h).1)
    (hidx : Index_4_6 o (m' + 1))
    (hev : Evaluation_ScSmooth E Q h310 H hCS hPF h322 h16 L) :
    ∃ (n : V.groupoid.OrbitSpace → ℝ) (U' : Set C.OrbitSpace),
      (dbarSection hTF hLF Fb h339 ιV hd c h).1.ControlsCompactness n U' ∧
      (∃ P : OrientedPerturbation (dbarSection hTF hLF Fb h339 ιV hd c h).1 m',
        P.IsAdmissible n U' ∧
        IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o P) ∧
      ∀ P₀ P₁ : OrientedPerturbation (dbarSection hTF hLF Fb h339 ιV hd c h).1 m',
        P₀.IsAdmissible n U' →
        IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o P₀ →
        P₁.IsAdmissible n U' →
        IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o P₁ →
        ∀ (τ : ManifoldForm (powModel E m) (Fin m → Q) (m' + 1))
          (hτ : ManifoldForm.ContMDiffForm (powModel E m) ∞ τ), ManifoldForm.extDeriv τ = 0 →
        ∀ η : ScForm (powClass E Q m) m',
          P₀.integral (ScMap.pullback (gwEv hev c) (m' + 1)
              (toScForm (powModel E m) (Fin m → Q) Homeomorph.ulift τ hτ + ScForm.d η)) =
            P₁.integral (ScMap.pullback (gwEv hev c) (m' + 1)
              (toScForm (powModel E m) (Fin m → Q) Homeomorph.ulift τ hτ)) := by
  obtain ⟨n, U', h1, h2, h3⟩ := memoir_theorem_1_12 h hbump hbd hcs o ho hidx (gwEv hev c)
  exact ⟨n, U', h1, h2, fun P₀ P₁ a₀ i₀ a₁ i₁ τ hτ hdτ η =>
    h3 P₀ P₁ a₀ i₀ a₁ i₁ _
      (d_toScForm_eq_zero _ hτ (extD_formFamily_eq_zero _ hτ hdτ)) η⟩

end GW

end GWMemoir
