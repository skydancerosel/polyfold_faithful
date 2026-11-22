import Polyfold.Chapter4.ScForms

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.4, p. 195:
the Whitney sum `TX ⊕ ⋯ ⊕ TX → X¹` of `k` copies of the tangent bundle of an M-polyfold `X`
("an easy exercise"), modelled on the tangent bundle of §2.3 (Definition 2.3.14, Proposition
2.3.15, Theorem 2.3.16, pp. 38–40).  Numbers and pages are the 2021 text's.

# The Whitney sum `⊕ₖ TX → X¹` as an M-polyfold bundle

## The text, paraphrased

(p. 195) The tangent `TX → X¹` has the structure of an sc-smooth bundle, and "it is an easy
exercise to show that the associated Whitney sum of `k` copies `TX ⊕ ⋯ ⊕ TX → X¹` is an sc-smooth
bundle".  (Remark 2.3.11, p. 38, and p. 40) `TX → X¹` is an M-polyfold bundle over `X¹`: the
projection is locally built on the bundle retractions `TO → O¹`, and the transition maps of the
charts are sc-smooth bundle maps (Theorem 2.3.16).

## What is formalized (namespace `Polyfold.MPolyfold`)

* `WhitneySum P k`: the points `(x, α₁, …, α_k)` with `x ∈ X¹` and `αᵢ ∈ T_xX`, a subspace of
  `X¹ × (TX)ᵏ` (so Hausdorff); `whitneyProj` (`⊕ₖ TX → X¹`), `whitneyVec` (`⊕ₖ TX → TX`, the
  `i`-th vector), `continuous_whitneyProj`, `continuous_whitneyVec`, and
  `metrizableSpace_whitneySum` (a subspace of a product of metrizable spaces, Theorem 2.3.10 and
  Proposition 2.3.15 (3)), hence `paracompactSpace_whitneySum`.
* `whitneyChart hφ v₀`: the chart `⊕ₖ Tφ : p⁻¹(V¹) → ⊕ₖ TO`,
  `(x, α₁, …, α_k) ↦ (φ(x), h₁, …, h_k)` with `Tφ(αᵢ) = (φ(x), hᵢ)`, onto the Whitney retract
  `(⊕ₖ TO, C¹ ⊕ Eᵏ, E¹ ⊕ Eᵏ)` of `ScForms.lean`; `whitneyChart_overlap`,
  `whitneyChart_transition` (`⊕ₖ Tψ ∘ (⊕ₖ Tφ)⁻¹ = ⊕ₖ T(ψ ∘ φ⁻¹)`), `whitneyChart_compatible`,
  and **`whitneyPolyfold P k`**: `⊕ₖ TX` as an M-polyfold.
* The bundle structure, **`whitneySum_bundle`** (the analogue of Theorem 2.3.16): the charts
  `⊕ₖ Tφ` belong to the structure, `p : ⊕ₖ TX → X¹` is sc-smooth and is the first projection onto
  the level chart `φ¹` in every chart, the models are bundle retracts (`⊕ₖ Tr` covers `r¹`, with
  the linear fibre maps `⊕ₖ Dr(x)`), and the transition maps are bundle maps covering the transition
  maps of the charts `φ¹`, with linear fibre maps `⊕ₖ D(ψ ∘ φ⁻¹)(x)`.
* The fibres: `whitneyFiberEquiv x : p⁻¹(x) ≃ (Fin k → T_xX)`; the fibre carries the linear
  structure of `(T_xX)ᵏ`, and in a chart `⊕ₖ Tφ` the fibre map is the linear isomorphism
  `(Tφ)ᵏ` (`whitneyChartMap_fiber`).
* The universal property of the fibred product (the Whitney sum is the `k`-fold fibred product of
  `TX` over `X¹`): `isScSmoothMap_whitneyProj`, `isScSmoothMap_whitneyVec`, and
  **`isScSmoothOn_whitneyLift`**: a map `g : Z → ⊕ₖ TX` is sc-smooth on an open set as soon as
  `p ∘ g : Z → X¹` and the `k` maps `prᵢ ∘ g : Z → TX` are.
* **`whitneyMapOf`** (`⊕ₖ Tf`, `(x, α₁, …, α_k) ↦ (f(x), Tf α₁, …, Tf α_k)`) for `f` sc-smooth,
  `isScSmoothMap_whitneyMapOf`, `whitneyMapOf_id`, `whitneyMapOf_comp` (the Whitney sum is a
  functor).
* `whitneyOneHomeomorph : ⊕₁ TX ≃ₜ TX` and `whitneyZeroHomeomorph : ⊕₀ TX ≃ₜ X¹`.

## Readings

* "An sc-smooth bundle" is read as Theorem 2.3.16 reads it for `TX → X¹`: an M-polyfold whose
  charts `⊕ₖ Tφ` are built on the bundle retractions `⊕ₖ Tr` covering `r¹`, sc-smooth projection,
  and transition maps that are sc-smooth bundle maps (fibrewise linear).  Part I's strong bundles
  (§2.6) are not used: like `TX → X¹`, the Whitney sum has no double filtration.
* The underlying set is `X¹ ×_{X¹} TX ×_{X¹} ⋯ ×_{X¹} TX` as a subspace of `X¹ × (TX)ᵏ`; for
  `k = 0` it is `X¹`.  The topology is the subspace topology; the charts `⊕ₖ Tφ` are
  homeomorphisms of the open sets `p⁻¹(V¹)` onto the Whitney retracts (`whitneyChart`).
-/

open Set Function Topology

noncomputable section

namespace Polyfold

/-! ### Local models: the projections of `⊕ₖ TO` and maps into it -/

section LocalModel

variable {E E' : ScBanach}

/-- The `i`-th vector `(y, h₁, …, h_k) ↦ (y, hᵢ)` of `E¹ ⊕ Eᵏ`, as an sc-operator into `TE`. -/
def ScBanach.whitneyCompOp (E : ScBanach) (k : ℕ) (i : Fin k) :
    ScOperator (E.whitney k) E.tangent where
  lvl m := (ContinuousLinearMap.id ℝ (E (m + 1))).prodMap
    ((ContinuousLinearMap.proj i).comp (E.fiberVecL m k))
  incl_comm _ q := Prod.ext rfl (E.fiberVecL_incl q.2 i).symm

lemma ScBanach.whitneyCompOp_zero (E : ScBanach) (k : ℕ) (i : Fin k) (q : (E.whitney k) 0) :
    E.whitneyCompOp k i 0 q = (q.1, ScBanach.whitneyVec q i) := rfl

/-- The base point `(y, h₁, …, h_k) ↦ y` is sc-smooth from `⊕ₖ TO` to `O¹`. -/
theorem isScSmoothRetractMap_whitney_fst {C O : Set (E 0)} (hO : IsScRetract E C O) (k : ℕ) :
    IsScSmoothRetractMap (E.whitney k) (E.whitneySet k C) (retractWhitney E C O k) E.shift
      (E.lvlSet C 1) (E.lvlSet O 1) Prod.fst :=
  (ScBanach.prodFstOp E.shift (E.fiberPow k)).isScSmoothRetractMap (hO.whitney k) fun _ hq => hq.1

/-- The `i`-th vector `(y, h₁, …, h_k) ↦ (y, hᵢ)` is sc-smooth from `⊕ₖ TO` to `TO`. -/
theorem isScSmoothRetractMap_whitneyComp {C O : Set (E 0)} (hO : IsScRetract E C O) (k : ℕ)
    (i : Fin k) :
    IsScSmoothRetractMap (E.whitney k) (E.whitneySet k C) (retractWhitney E C O k) E.tangent
      (E.tangentSet C) (retractTangent E C O) (E.whitneyCompOp k i 0) :=
  (E.whitneyCompOp k i).isScSmoothRetractMap (hO.whitney k) fun _ hq => hq.2 i

/-- The zero map into `E⁰ = 0` is sc-smooth. -/
theorem isScSmoothRetractMap_fiberPow_zero {C O : Set (E' 0)} (hO : IsScRetract E' C O) :
    IsScSmoothRetractMap E' C O (E.fiberPow 0) univ univ (fun _ => 0) :=
  (show ScOperator E' (E.fiberPow 0) from
    { lvl := fun _ => 0, incl_comm := fun _ _ => Subsingleton.elim (α := Fin 0 → ℝ) _ _ }
    ).isScSmoothRetractMap hO (mapsTo_univ _ _)

/-- The packing `y ↦ (F₁(y), …, F_k(y))` of `k` sc-smooth maps into `Eᵏ` is sc-smooth. -/
theorem isScSmoothRetractMap_fiberPack {C O : Set (E' 0)} (hO : IsScRetract E' C O) :
    ∀ (k : ℕ) (F : Fin k → E' 0 → E 0),
      (∀ i, IsScSmoothRetractMap E' C O E univ univ (F i)) →
        IsScSmoothRetractMap E' C O (E.fiberPow k) univ univ
          (fun y => E.fiberPackL 0 k (fun i => F i y))
  | 0, F, _ => (isScSmoothRetractMap_fiberPow_zero hO).congr fun y _ =>
      Subsingleton.elim (α := Fin 0 → ℝ) _ _
  | k + 1, F, hF => by
    have h := isScSmoothRetractMap_fiberPack hO k (fun i => F i.succ) fun i => hF i.succ
    exact (IsScSmoothRetractMap.scPair (hF 0) h (mapsTo_univ _ _) :
      IsScSmoothRetractMap E' C O (E.prod (E.fiberPow k)) univ univ _)

/-- **Maps into `⊕ₖ TO` in a local model**: if `F₀ : O' → O¹` and `Fᵢ : O' → TO` are sc-smooth
and the `Fᵢ` lie over `F₀`, then `y ↦ (F₀(y), (F₁ y)₂, …, (F_k y)₂)` is sc-smooth into `⊕ₖ TO`. -/
theorem IsScSmoothRetractMap.whitneyMk {C' O' : Set (E' 0)} (hO' : IsScRetract E' C' O')
    {C O : Set (E 0)} (hO : IsScRetract E C O) {k : ℕ} {F₀ : E' 0 → E 1}
    {F : Fin k → E' 0 → E.tangent 0}
    (h₀ : IsScSmoothRetractMap E' C' O' E.shift (E.lvlSet C 1) (E.lvlSet O 1) F₀)
    (hF : ∀ i, IsScSmoothRetractMap E' C' O' E.tangent (E.tangentSet C) (retractTangent E C O)
      (F i))
    (hfst : ∀ y ∈ O', ∀ i, (F i y).1 = F₀ y) :
    IsScSmoothRetractMap E' C' O' (E.whitney k) (E.whitneySet k C) (retractWhitney E C O k)
      (fun y => ScBanach.whitneyMk (F₀ y) (fun i => (F i y).2)) := by
  have hsnd : ∀ i, IsScSmoothRetractMap E' C' O' E univ univ (fun y => (F i y).2) := fun i =>
    ((ScBanach.prodSndOp E.shift E).isScSmoothRetractMap hO.tangentSet
      (mapsTo_univ _ _)).comp (hF i) hO.tangentSet
  have hpack := isScSmoothRetractMap_fiberPack hO' k _ hsnd
  refine (IsScSmoothRetractMap.scPair h₀ hpack (C' := E.whitneySet k C)
    (O' := retractWhitney E C O k) ?_ :)
  intro y hy
  refine mem_retractWhitney_mk.2 ⟨h₀.mapsTo hy, fun i => ?_⟩
  have := (hF i).mapsTo hy
  rwa [← hfst y hy i]

/-! ### The bundle structure (the analogue of Theorem 2.3.16) -/


/-- The fibre map `(h₁, …, h_k) ↦ (A h₁, …, A h_k)` of `Eᵏ → Fᵏ` for a linear `A : E → F`. -/
def fiberPowMap {F : ScBanach} (k : ℕ) (A : E 0 →L[ℝ] F 0) :
    (E.fiberPow k) 0 →L[ℝ] (F.fiberPow k) 0 :=
  (F.fiberPackL 0 k).comp ((ContinuousLinearMap.pi fun i : Fin k =>
    A.comp (ContinuousLinearMap.proj i)).comp (E.fiberVecL 0 k))

lemma fiberPowMap_apply {F : ScBanach} (k : ℕ) (A : E 0 →L[ℝ] F 0) (h : Fin k → E 0) :
    fiberPowMap k A (E.fiberPackL 0 k h) = F.fiberPackL 0 k (fun i => A (h i)) := by
  simp only [fiberPowMap, ContinuousLinearMap.comp_apply, ScBanach.fiberVecL_fiberPackL]
  rfl

/-- **The models of `⊕ₖ TX` are bundle retracts** (2021 Definition 2.1.16): `⊕ₖ Tr` covers `r¹`,
`(⊕ₖ Tr)(y, h₁, …, h_k) = (r(y), Dr(y)h₁, …, Dr(y)h_k)`, with fibre maps linear. -/
theorem ScRetraction.whitney_isBundleRetractionOver {C : Set (E 0)} (R : ScRetraction E C)
    (k : ℕ) :
    ScRetraction.IsBundleRetractionOver (E := E.shift) (F := E.fiberPow k) (R.whitney k)
      R.shift := by
  refine ⟨?_, fun y => fiberPowMap k (scDeriv R.U R y), fun p hp => ?_⟩
  · ext p; simp [ScRetraction.whitney_U, ScBanach.whitneySet, ScRetraction.shift_U]
  · rw [R.whitney_apply, whitneyMap_eq_mk]
    refine Prod.ext rfl ?_
    conv_rhs => rw [← whitneyMk_fst_vec p]
    exact (fiberPowMap_apply k _ _).symm


end LocalModel

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
  (k : ℕ)

/-! ### The space `⊕ₖ TX` -/

/-- **The Whitney sum `⊕ₖ TX`** of `k` copies of the tangent bundle (2021 p. 195): the points
`(x, α₁, …, α_k)` with `x ∈ X¹` and `αᵢ ∈ T_xX`, a subspace of `X¹ × (TX)ᵏ`. -/
def WhitneySum : Type (max u 1) :=
  {v : P.Level 1 × (Fin k → P.TangentSpace) // ∀ i, P.tangentProj (v.2 i) = v.1}

instance : TopologicalSpace (P.WhitneySum k) :=
  inferInstanceAs (TopologicalSpace
    {v : P.Level 1 × (Fin k → P.TangentSpace) // ∀ i, P.tangentProj (v.2 i) = v.1})

instance : T2Space (P.WhitneySum k) :=
  inferInstanceAs (T2Space
    {v : P.Level 1 × (Fin k → P.TangentSpace) // ∀ i, P.tangentProj (v.2 i) = v.1})

/-- `⊕ₖ TX` is metrizable (a subspace of `X¹ × (TX)ᵏ`, Theorem 2.3.10 and Proposition 2.3.15
(3)). -/
theorem metrizableSpace_whitneySum : TopologicalSpace.MetrizableSpace (P.WhitneySum k) := by
  have := P.metrizableSpace_level 1
  have := P.metrizableSpace_tangentSpace
  exact IsEmbedding.subtypeVal.metrizableSpace (Y := P.Level 1 × (Fin k → P.TangentSpace))

instance paracompactSpace_whitneySum : ParacompactSpace (P.WhitneySum k) :=
  haveI := P.metrizableSpace_whitneySum k
  paracompactSpace_of_metrizableSpace _

variable {P k}

/-- The projection `p : ⊕ₖ TX → X¹`. -/
def whitneyProj (v : P.WhitneySum k) : P.Level 1 := v.1.1

/-- The `i`-th vector `prᵢ : ⊕ₖ TX → TX`. -/
def whitneyVec (v : P.WhitneySum k) (i : Fin k) : P.TangentSpace := v.1.2 i

lemma tangentProj_whitneyVec (v : P.WhitneySum k) (i : Fin k) :
    P.tangentProj (whitneyVec v i) = whitneyProj v := v.2 i

lemma whitneyVec_mem_fiber (v : P.WhitneySum k) (i : Fin k) :
    whitneyVec v i ∈ P.tangentFiber (whitneyProj v) := v.2 i

/-- The point `(x, α₁, …, α_k)` of `⊕ₖ TX`. -/
def whitneyMk (x : P.Level 1) (α : Fin k → P.TangentSpace)
    (hα : ∀ i, P.tangentProj (α i) = x) : P.WhitneySum k := ⟨(x, α), hα⟩

@[simp] lemma whitneyProj_mk (x : P.Level 1) (α : Fin k → P.TangentSpace)
    (hα : ∀ i, P.tangentProj (α i) = x) : whitneyProj (whitneyMk x α hα) = x := rfl

@[simp] lemma whitneyVec_mk (x : P.Level 1) (α : Fin k → P.TangentSpace)
    (hα : ∀ i, P.tangentProj (α i) = x) (i : Fin k) : whitneyVec (whitneyMk x α hα) i = α i := rfl

@[ext] lemma whitneySum_ext {v w : P.WhitneySum k} (h₁ : whitneyProj v = whitneyProj w)
    (h₂ : ∀ i, whitneyVec v i = whitneyVec w i) : v = w :=
  Subtype.ext (Prod.ext h₁ (funext h₂))

theorem continuous_whitneyProj : Continuous (whitneyProj : P.WhitneySum k → P.Level 1) :=
  continuous_fst.comp continuous_subtype_val

theorem continuous_whitneyVec (i : Fin k) :
    Continuous (fun v : P.WhitneySum k => whitneyVec v i) :=
  (continuous_apply i).comp (continuous_snd.comp continuous_subtype_val)

/-- A map into `⊕ₖ TX` is continuous iff its base and its `k` vectors are. -/
theorem continuousOn_whitney_iff {Z : Type*} [TopologicalSpace Z] {g : Z → P.WhitneySum k}
    {s : Set Z} : ContinuousOn g s ↔
      ContinuousOn (fun z => whitneyProj (g z)) s ∧
        ∀ i, ContinuousOn (fun z => whitneyVec (g z) i) s := by
  have hind : IsInducing (Subtype.val : P.WhitneySum k → P.Level 1 × (Fin k → P.TangentSpace)) :=
    IsInducing.subtypeVal
  refine Iff.trans (hind.continuousOn_iff (f := g) (s := s)) ?_
  constructor
  · intro h
    exact ⟨continuous_fst.comp_continuousOn h, fun i =>
      ((continuous_apply i).comp continuous_snd).comp_continuousOn h⟩
  · rintro ⟨h₁, h₂⟩
    exact h₁.prodMk (continuousOn_pi.2 h₂)

/-! ### The charts `⊕ₖ Tφ` -/

section Chart

open scoped Classical

variable {φ ψ : MChart X}

variable (φ) in
/-- `p⁻¹(V¹)`, the part of `⊕ₖ TX` over the domain of the chart `φ`. -/
def whitneyChartSet : Set (P.WhitneySum k) := {v | P.levelVal 1 (whitneyProj v) ∈ φ.source}

lemma whitneyVec_mem_tangentChartSet {v : P.WhitneySum k} (hv : v ∈ whitneyChartSet (k := k) φ)
    (i : Fin k) : whitneyVec v i ∈ tangentChartSet (P := P) φ :=
  mem_tangentChartSet_of_mem_fiber hv (whitneyVec_mem_fiber v i)

/-- **The chart map `⊕ₖ Tφ`**: `(x, α₁, …, α_k) ↦ (φ(x), h₁, …, h_k)`, `Tφ(αᵢ) = (φ(x), hᵢ)`. -/
def whitneyChartMap (hφ : P.IsChart φ) (v : P.WhitneySum k) : (φ.model.E.whitney k) 0 :=
  ScBanach.whitneyMk (levelLift φ 1 (P.levelVal 1 (whitneyProj v)))
    (fun i => (tangentChartMap hφ (whitneyVec v i)).2)

variable (hφ : P.IsChart φ)

lemma whitneyChartMap_fst (v : P.WhitneySum k) :
    (whitneyChartMap hφ v).1 = levelLift φ 1 (P.levelVal 1 (whitneyProj v)) := rfl

@[simp] lemma whitneyVec_whitneyChartMap (v : P.WhitneySum k) (i : Fin k) :
    ScBanach.whitneyVec (whitneyChartMap hφ v) i = (tangentChartMap hφ (whitneyVec v i)).2 :=
  congrFun (ScBanach.whitneyVec_mk _ _) i

/-- The `i`-th vector of the chart image together with the base point is `Tφ(αᵢ)`. -/
lemma whitneyChartMap_pair {v : P.WhitneySum k} (hv : v ∈ whitneyChartSet (k := k) φ)
    (i : Fin k) :
    (((whitneyChartMap hφ v).1, ScBanach.whitneyVec (whitneyChartMap hφ v) i) :
      φ.model.E.tangent 0) = tangentChartMap hφ (whitneyVec v i) := by
  refine Prod.ext ?_ ?_
  · rw [whitneyChartMap_fst, tangentChartMap_fst_of_mem_fiber hφ hv (whitneyVec_mem_fiber v i)]
  · exact whitneyVec_whitneyChartMap hφ v i

lemma whitneyChartMap_mem {v : P.WhitneySum k} (hv : v ∈ whitneyChartSet (k := k) φ) :
    whitneyChartMap hφ v ∈ retractWhitney φ.model.E φ.model.C φ.model.O k := by
  refine ⟨levelLift_mem_lvlSet_one hφ hv, fun i => ?_⟩
  rw [whitneyChartMap_pair hφ hv i]
  exact tangentChartMap_mem hφ (whitneyVec_mem_tangentChartSet hv i)

lemma mk_ofVec_congr {a b : φ.model.E.tangent 0}
    (ha : a ∈ retractTangent φ.model.E φ.model.C φ.model.O)
    (hb : b ∈ retractTangent φ.model.E φ.model.C φ.model.O) (hab : a = b) :
    TangentSpace.mk (TangentPre.ofVec hφ ha) = TangentSpace.mk (TangentPre.ofVec hφ hb) := by
  subst hab; rfl

/-- The point `(φ⁻¹(y), (Tφ)⁻¹(y, h₁), …, (Tφ)⁻¹(y, h_k))` of a point of `⊕ₖ TO`. -/
def whitneyOfVec {q : (φ.model.E.whitney k) 0}
    (hq : q ∈ retractWhitney φ.model.E φ.model.C φ.model.O k) : P.WhitneySum k :=
  whitneyMk (chartPoint hφ hq.1) (fun i => TangentSpace.mk (TangentPre.ofVec hφ (hq.2 i)))
    fun i => mk_ofVec_mem_fiber_chartPoint hφ hq.1 (hq.2 i)

lemma whitneyOfVec_mem {q : (φ.model.E.whitney k) 0}
    (hq : q ∈ retractWhitney φ.model.E φ.model.C φ.model.O k) :
    whitneyOfVec hφ hq ∈ whitneyChartSet (k := k) φ :=
  chartPoint_mem_source hφ hq.1

lemma whitneyChartMap_whitneyOfVec {q : (φ.model.E.whitney k) 0}
    (hq : q ∈ retractWhitney φ.model.E φ.model.C φ.model.O k) :
    whitneyChartMap hφ (whitneyOfVec hφ hq) = q := by
  conv_rhs => rw [← whitneyMk_fst_vec q]
  refine Prod.ext (levelLift_chartPoint hφ hq.1) (congrArg (φ.model.E.fiberPackL 0 k) ?_)
  funext i
  change (tangentChartMap hφ (TangentSpace.mk (TangentPre.ofVec hφ (hq.2 i)))).2 = _
  rw [tangentChartMap_mk_ofVec]

lemma whitneyOfVec_whitneyChartMap {v : P.WhitneySum k} (hv : v ∈ whitneyChartSet (k := k) φ) :
    whitneyOfVec hφ (whitneyChartMap_mem hφ hv) = v := by
  ext i
  · exact chartPoint_levelLift hφ hv
  · change TangentSpace.mk (TangentPre.ofVec hφ ((whitneyChartMap_mem hφ hv).2 i)) = _
    rw [mk_ofVec_congr hφ _ (tangentChartMap_mem hφ (whitneyVec_mem_tangentChartSet hv i))
      (whitneyChartMap_pair hφ hv i)]
    exact mk_ofVec_tangentChartMap hφ (whitneyVec_mem_tangentChartSet hv i)

lemma whitneyProj_whitneyOfVec {q : (φ.model.E.whitney k) 0}
    (hq : q ∈ retractWhitney φ.model.E φ.model.C φ.model.O k) :
    whitneyProj (whitneyOfVec hφ hq) = chartPoint hφ hq.1 := rfl

lemma whitneyVec_whitneyOfVec {q : (φ.model.E.whitney k) 0}
    (hq : q ∈ retractWhitney φ.model.E φ.model.C φ.model.O k) (i : Fin k) :
    whitneyVec (whitneyOfVec hφ hq) i = TangentSpace.mk (TangentPre.ofVec hφ (hq.2 i)) := rfl

/-- `⊕ₖ Tφ` is continuous on `p⁻¹(V¹)`. -/
theorem continuousOn_whitneyChartMap :
    ContinuousOn (whitneyChartMap (k := k) hφ) (whitneyChartSet φ) := by
  intro v hv
  have h1 : ContinuousWithinAt
      (fun w : P.WhitneySum k => levelLift φ 1 (P.levelVal 1 (whitneyProj w)))
      (whitneyChartSet φ) v :=
    ((levelChart hφ (whitneyProj v)).continuousOn_toFun.comp continuous_whitneyProj.continuousOn
      fun w hw => hw) v hv
  have h2 : ∀ i, ContinuousWithinAt
      (fun w : P.WhitneySum k => (tangentChartMap hφ (whitneyVec w i)).2) (whitneyChartSet φ) v :=
    fun i => (continuous_snd.comp_continuousOn
      ((tangentChart hφ (whitneyVec v i)).continuousOn_toFun.comp
        (continuous_whitneyVec i).continuousOn fun w hw => whitneyVec_mem_tangentChartSet hw i))
      v hv
  exact h1.prodMk ((φ.model.E.fiberPackL 0 k).continuous.continuousAt.comp_continuousWithinAt
    (continuousWithinAt_pi.2 h2))

/-- The inverse `(⊕ₖ Tφ)⁻¹ : ⊕ₖ TO → p⁻¹(V¹)`, with the junk value `v₀` off `⊕ₖ TO`. -/
def whitneyChartInv (v₀ : P.WhitneySum k) (q : (φ.model.E.whitney k) 0) : P.WhitneySum k :=
  if hq : q ∈ retractWhitney φ.model.E φ.model.C φ.model.O k then whitneyOfVec hφ hq else v₀

lemma whitneyChartInv_of_mem (v₀ : P.WhitneySum k) {q : (φ.model.E.whitney k) 0}
    (hq : q ∈ retractWhitney φ.model.E φ.model.C φ.model.O k) :
    whitneyChartInv hφ v₀ q = whitneyOfVec hφ hq := dif_pos hq

/-- `(⊕ₖ Tφ)⁻¹` is continuous on `⊕ₖ TO`. -/
theorem continuousOn_whitneyChartInv (v₀ : P.WhitneySum k) :
    ContinuousOn (whitneyChartInv hφ v₀) (retractWhitney φ.model.E φ.model.C φ.model.O k) := by
  rw [continuousOn_whitney_iff]
  refine ⟨fun q hq => ?_, fun i q hq => ?_⟩
  · have hc : ContinuousOn (fun q : (φ.model.E.whitney k) 0 =>
        (levelChart hφ (chartPoint hφ hq.1)).symm q.1)
        (retractWhitney φ.model.E φ.model.C φ.model.O k) :=
      (levelChart hφ (chartPoint hφ hq.1)).continuousOn_invFun.comp continuous_fst.continuousOn
        fun q hq => hq.1
    refine (hc.congr fun q' hq' => ?_) q hq
    rw [whitneyChartInv_of_mem hφ v₀ hq', whitneyProj_whitneyOfVec]
    apply level_ext
    rw [levelChart_symm_apply hφ _ hq'.1]
    rfl
  · have hc : ContinuousOn (fun q : (φ.model.E.whitney k) 0 =>
        (tangentChart hφ (TangentSpace.mk (TangentPre.ofVec hφ (hq.2 i)))).symm
          (q.1, ScBanach.whitneyVec q i))
        (retractWhitney φ.model.E φ.model.C φ.model.O k) :=
      (tangentChart hφ _).continuousOn_invFun.comp
        (continuous_fst.prodMk (((continuous_apply i).comp
          (φ.model.E.fiberVecL 0 k).continuous).comp continuous_snd)).continuousOn
        fun q hq => hq.2 i
    refine (hc.congr fun q' hq' => ?_) q hq
    rw [whitneyChartInv_of_mem hφ v₀ hq', whitneyVec_whitneyOfVec]
    exact (tangentChartInv_of_mem hφ _ (hq'.2 i)).symm

lemma whitneyChartInv_mem (v₀ : P.WhitneySum k) {q : (φ.model.E.whitney k) 0}
    (hq : q ∈ retractWhitney φ.model.E φ.model.C φ.model.O k) :
    whitneyChartInv hφ v₀ q ∈ whitneyChartSet (k := k) φ := by
  rw [whitneyChartInv_of_mem hφ v₀ hq]; exact whitneyOfVec_mem hφ hq

lemma whitneyChartInv_whitneyChartMap (v₀ : P.WhitneySum k) {v : P.WhitneySum k}
    (hv : v ∈ whitneyChartSet (k := k) φ) : whitneyChartInv hφ v₀ (whitneyChartMap hφ v) = v := by
  rw [whitneyChartInv_of_mem hφ v₀ (whitneyChartMap_mem hφ hv)]
  exact whitneyOfVec_whitneyChartMap hφ hv

lemma whitneyChartMap_whitneyChartInv (v₀ : P.WhitneySum k) {q : (φ.model.E.whitney k) 0}
    (hq : q ∈ retractWhitney φ.model.E φ.model.C φ.model.O k) :
    whitneyChartMap hφ (whitneyChartInv hφ v₀ q) = q := by
  rw [whitneyChartInv_of_mem hφ v₀ hq]; exact whitneyChartMap_whitneyOfVec hφ hq

/-- **The chart `(p⁻¹(V¹), ⊕ₖ Tφ, (⊕ₖ TO, C¹ ⊕ Eᵏ, E¹ ⊕ Eᵏ))` of `⊕ₖ TX`** induced by the chart
`φ` of `X`, with the junk value `v₀` of the inverse off `⊕ₖ TO`. -/
def whitneyChart (v₀ : P.WhitneySum k) : MChart (P.WhitneySum k) where
  model := φ.model.whitney k
  toPartialEquiv :=
    { toFun := whitneyChartMap hφ
      invFun := whitneyChartInv hφ v₀
      source := whitneyChartSet φ
      target := retractWhitney φ.model.E φ.model.C φ.model.O k
      map_source' := fun _ hv => whitneyChartMap_mem hφ hv
      map_target' := fun _ hq => whitneyChartInv_mem hφ v₀ hq
      left_inv' := fun _ hv => whitneyChartInv_whitneyChartMap hφ v₀ hv
      right_inv' := fun _ hq => whitneyChartMap_whitneyChartInv hφ v₀ hq }
  isOpen_source := φ.isOpen_source.preimage ((continuous_levelVal 1).comp continuous_whitneyProj)
  target_eq := rfl
  continuousOn_toFun := continuousOn_whitneyChartMap hφ
  continuousOn_invFun := continuousOn_whitneyChartInv hφ v₀

variable (v₀ : P.WhitneySum k)

lemma whitneyChart_source : (whitneyChart hφ v₀).source = whitneyChartSet φ := rfl

lemma whitneyChart_apply (v : P.WhitneySum k) : whitneyChart hφ v₀ v = whitneyChartMap hφ v := rfl

lemma whitneyChart_model : (whitneyChart hφ v₀).model = φ.model.whitney k := rfl

lemma whitneyChart_symm_apply {q : (φ.model.E.whitney k) 0}
    (hq : q ∈ retractWhitney φ.model.E φ.model.C φ.model.O k) :
    (whitneyChart hφ v₀).symm q = whitneyOfVec hφ hq := whitneyChartInv_of_mem hφ v₀ hq

/-- `⊕ₖ Tφ(p⁻¹(V¹) ∩ p⁻¹(V'¹)) = ⊕ₖ T(φ(V ∩ V'))`. -/
theorem whitneyChart_overlap (hψ : P.IsChart ψ) (w₀ : P.WhitneySum k) :
    (whitneyChart hφ v₀).overlap (whitneyChart hψ w₀) =
      retractWhitney φ.model.E φ.model.C (φ.overlap ψ) k := by
  obtain ⟨W, hW, hWeq⟩ := exists_overlap_eq_inter (φ := φ) ψ
  rw [hWeq, retractWhitney_inter_isOpen φ.model.isScRetract hW]
  ext q
  constructor
  · rintro ⟨v, ⟨hv, hv'⟩, rfl⟩
    refine ⟨whitneyChartMap_mem hφ hv, ?_⟩
    change φ.model.E.toBase 1 (levelLift φ 1 (P.levelVal 1 (whitneyProj v))) ∈ W
    rw [P.toBase_levelLift hφ hv (levelVal_mem _)]
    have : φ (P.levelVal 1 (whitneyProj v)) ∈ φ.overlap ψ := φ.mem_overlap ψ hv hv'
    rw [hWeq] at this
    exact this.2
  · rintro ⟨hq, hqW⟩
    refine ⟨whitneyOfVec hφ hq, ⟨whitneyOfVec_mem hφ hq, ?_⟩, whitneyChartMap_whitneyOfVec hφ hq⟩
    change P.levelVal 1 (chartPoint hφ hq.1) ∈ ψ.source
    rw [levelVal_chartPoint]
    have : φ.model.E.toBase 1 q.1 ∈ φ.overlap ψ := by rw [hWeq]; exact ⟨hq.1, hqW⟩
    obtain ⟨y, hy, hyeq⟩ := this
    rw [← hyeq, φ.symm_apply_apply hy.1]
    exact hy.2

/-- **The transition maps**: `⊕ₖ Tψ ∘ (⊕ₖ Tφ)⁻¹ = ⊕ₖ T(ψ ∘ φ⁻¹)` on `⊕ₖ T(φ(V ∩ V'))`. -/
theorem whitneyChart_transition (hψ : P.IsChart ψ) (w₀ : P.WhitneySum k)
    {q : (φ.model.E.whitney k) 0} (hq : q ∈ retractWhitney φ.model.E φ.model.C (φ.overlap ψ) k) :
    (whitneyChart hφ v₀).transition (whitneyChart hψ w₀) q =
      retractWhitneyMap φ.model.E φ.model.C (φ.overlap ψ) (φ.transition ψ) k q := by
  have hq' := retractWhitney_overlap_subset (k := k) ψ hq
  change whitneyChartMap hψ ((whitneyChart hφ v₀).symm q) = _
  rw [whitneyChart_symm_apply hφ v₀ hq']
  set x := chartPoint hφ hq'.1
  have hx : P.levelVal 1 x ∈ φ.source := chartPoint_mem_source hφ hq'.1
  have hx' : P.levelVal 1 x ∈ ψ.source := by
    obtain ⟨z, hz, hzeq⟩ := (show φ.model.E.toBase 1 q.1 ∈ φ.overlap ψ from hq.1)
    rw [levelVal_chartPoint, ← hzeq, φ.symm_apply_apply hz.1]; exact hz.2
  have hlift : levelLift φ 1 (P.levelVal 1 x) = q.1 := levelLift_chartPoint hφ hq'.1
  refine Prod.ext ?_ (congrArg (ψ.model.E.fiberPackL 0 k) (funext fun i => ?_))
  · change levelLift ψ 1 (P.levelVal 1 x) = levelMap (φ.transition ψ) 1 q.1
    rw [← hlift, levelMap_transition_levelLift hφ hψ hx hx']
  · change (tangentChartMap hψ (TangentSpace.mk (TangentPre.ofVec hφ (hq'.2 i)))).2 = _
    rw [tangentChartMap_mk_ofVec_of_mem hφ hψ (hq'.2 i) (hq.2 i)]

/-- The charts `⊕ₖ Tφ` are sc-smoothly compatible: the transition maps are the Whitney sums
`⊕ₖ T(ψ ∘ φ⁻¹)` of the transition maps of `X` (`IsScSmoothRetractMap.whitney`). -/
theorem whitneyChart_compatible (hψ : P.IsChart ψ) (w₀ : P.WhitneySum k) :
    (whitneyChart hφ v₀).Compatible (whitneyChart hψ w₀) := by
  have key : ∀ (φ ψ : MChart X) (hφ : P.IsChart φ) (hψ : P.IsChart ψ) (v₀ w₀ : P.WhitneySum k),
      IsScSmoothRetractMap (whitneyChart hφ v₀).model.E (whitneyChart hφ v₀).model.C
        ((whitneyChart hφ v₀).overlap (whitneyChart hψ w₀)) (whitneyChart hψ w₀).model.E
        (whitneyChart hψ w₀).model.C ((whitneyChart hψ w₀).overlap (whitneyChart hφ v₀))
        ((whitneyChart hφ v₀).transition (whitneyChart hψ w₀)) := by
    intro φ ψ hφ hψ v₀ w₀
    rw [whitneyChart_overlap, whitneyChart_overlap]
    have := (hφ.compatible hψ (P := P)).1.whitney (φ.isScRetract_overlap ψ)
      (ψ.isScRetract_overlap φ) k
    exact this.congr fun a ha => (whitneyChart_transition hφ v₀ hψ w₀ ha).symm
  exact ⟨key φ ψ hφ hψ v₀ w₀, key ψ φ hψ hφ w₀ v₀⟩

end Chart

variable (P k) in
/-- The atlas `⊕ₖ Tφ` of `⊕ₖ TX`. -/
def whitneyAtlas : MAtlas (P.WhitneySum k) where
  charts := {χ | ∃ (φ : MChart X) (hφ : P.IsChart φ) (v₀ : P.WhitneySum k),
    χ = whitneyChart hφ v₀}
  compatible := by
    rintro _ ⟨φ, hφ, v₀, rfl⟩ _ ⟨ψ, hψ, w₀, rfl⟩
    exact whitneyChart_compatible hφ v₀ hψ w₀
  cover v := by
    obtain ⟨φ, hφ, hx⟩ := P.exists_isChart_mem_source (P.levelVal 1 (whitneyProj v))
    exact ⟨whitneyChart hφ v, ⟨φ, hφ, v, rfl⟩, hx⟩

variable (P k) in
/-- **The Whitney sum `⊕ₖ TX` as an M-polyfold** (2021 p. 195), with the charts `⊕ₖ Tφ`. -/
def whitneyPolyfold : MPolyfold (P.WhitneySum k) where
  atlas := P.whitneyAtlas k

theorem whitneyPolyfold_isChart {φ : MChart X} (hφ : P.IsChart φ) (v₀ : P.WhitneySum k) :
    (P.whitneyPolyfold k).IsChart (whitneyChart hφ v₀) :=
  (P.whitneyPolyfold k).isChart_of_mem ⟨φ, hφ, v₀, rfl⟩

/-! ### The projections are sc-smooth -/

section Projections

variable [ParacompactSpace (P.Level 1)]

/-- **`p : ⊕ₖ TX → X¹` is sc-smooth**: in the charts `⊕ₖ Tφ` and `φ¹` it is the projection
`⊕ₖ TO → O¹`. -/
theorem isScSmoothMap_whitneyProj :
    (P.whitneyPolyfold k).IsScSmoothMap P.shift (whitneyProj (P := P) (k := k)) := by
  refine IsScSmoothOn.of_exists_charts isOpen_univ continuous_whitneyProj.continuousOn
    fun v _ => ?_
  obtain ⟨φ, hφ, hx⟩ := P.exists_isChart_mem_source (P.levelVal 1 (whitneyProj v))
  refine ⟨whitneyChart hφ v, levelChart hφ (whitneyProj v), whitneyChartSet φ,
    whitneyPolyfold_isChart hφ v, P.shift_isChart hφ _, (whitneyChart hφ v).isOpen_source, hx,
    fun w hw => ⟨mem_univ _, hw⟩, fun w hw => hw, ?_⟩
  have himg : whitneyChart hφ v '' whitneyChartSet φ =
      retractWhitney φ.model.E φ.model.C φ.model.O k := (whitneyChart hφ v).image_source
  rw [himg]
  refine (isScSmoothRetractMap_whitney_fst φ.model.isScRetract k).congr fun q hq => ?_
  change q.1 = levelLift φ 1 (P.levelVal 1 (whitneyProj (whitneyChartInv hφ v q)))
  rw [← whitneyChartMap_fst hφ, whitneyChartMap_whitneyChartInv hφ v hq]

end Projections

/-- **`prᵢ : ⊕ₖ TX → TX` is sc-smooth**: in the charts `⊕ₖ Tφ` and `Tφ` it is the projection
`(y, h₁, …, h_k) ↦ (y, hᵢ)`. -/
theorem isScSmoothMap_whitneyVec (i : Fin k) :
    (P.whitneyPolyfold k).IsScSmoothMap P.tangentPolyfold
      (fun v : P.WhitneySum k => whitneyVec v i) := by
  refine IsScSmoothOn.of_exists_charts isOpen_univ (continuous_whitneyVec i).continuousOn
    fun v _ => ?_
  obtain ⟨φ, hφ, hx⟩ := P.exists_isChart_mem_source (P.levelVal 1 (whitneyProj v))
  refine ⟨whitneyChart hφ v, tangentChart hφ (whitneyVec v i), whitneyChartSet φ,
    whitneyPolyfold_isChart hφ v, P.tangentPolyfold_isChart hφ _,
    (whitneyChart hφ v).isOpen_source, hx, fun w hw => ⟨mem_univ _, hw⟩,
    fun w hw => whitneyVec_mem_tangentChartSet hw i, ?_⟩
  have himg : whitneyChart hφ v '' whitneyChartSet φ =
      retractWhitney φ.model.E φ.model.C φ.model.O k := (whitneyChart hφ v).image_source
  rw [himg]
  refine (isScSmoothRetractMap_whitneyComp φ.model.isScRetract k i).congr fun q hq => ?_
  change _ = tangentChartMap hφ (whitneyVec (whitneyChartInv hφ v q) i)
  rw [ScBanach.whitneyCompOp_zero, ← whitneyChartMap_pair hφ (whitneyChartInv_mem hφ v hq),
    whitneyChartMap_whitneyChartInv hφ v hq]

/-! ### Maps into `⊕ₖ TX`: the universal property of the fibred product -/

section Lift

universe w

variable {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {Q : MPolyfold Z}
  [ParacompactSpace (P.Level 1)]

/-- **A map into `⊕ₖ TX` is sc-smooth on an open set if its base `p ∘ g : Z → X¹` and its `k`
vectors `prᵢ ∘ g : Z → TX` are** (`⊕ₖ TX` is the `k`-fold fibred product of `TX` over `X¹`). -/
theorem isScSmoothOn_whitneyLift {g : Z → P.WhitneySum k} {U : Set Z}
    (h₀ : Q.IsScSmoothOn P.shift (fun z => whitneyProj (g z)) U)
    (h : ∀ i, Q.IsScSmoothOn P.tangentPolyfold (fun z => whitneyVec (g z) i) U) :
    Q.IsScSmoothOn (P.whitneyPolyfold k) g U := by
  have hcont : ContinuousOn g U :=
    continuousOn_whitney_iff.2 ⟨h₀.continuousOn, fun i => (h i).continuousOn⟩
  refine IsScSmoothOn.of_exists_charts h₀.isOpen hcont fun z hz => ?_
  obtain ⟨φ', hφ', hzφ'⟩ := Q.exists_isChart_mem_source z
  obtain ⟨φ, hφ, hx⟩ := P.exists_isChart_mem_source (P.levelVal 1 (whitneyProj (g z)))
  set V := (U ∩ φ'.source) ∩ g ⁻¹' whitneyChartSet φ with hV
  have hVo : IsOpen V := (hcont.mono inter_subset_left).isOpen_inter_preimage
    (h₀.isOpen.inter φ'.isOpen_source) (whitneyChart hφ (g z)).isOpen_source
  have hVsub : V ⊆ U ∩ φ'.source := inter_subset_left
  refine ⟨φ', whitneyChart hφ (g z), V, hφ', whitneyPolyfold_isChart hφ _, hVo,
    ⟨⟨hz, hzφ'⟩, hx⟩, hVsub, fun y hy => hy.2, ?_⟩
  have hs₀ := h₀.smooth φ' (levelChart hφ (whitneyProj (g z))) hφ' (P.shift_isChart hφ _) V hVo
    hVsub fun y hy => hy.2
  have hs : ∀ i, IsScSmoothRetractMap φ'.model.E φ'.model.C (φ' '' V) φ.model.E.tangent
      (φ.model.E.tangentSet φ.model.C) (retractTangent φ.model.E φ.model.C φ.model.O)
      ((tangentChart hφ (whitneyVec (g z) i)) ∘ (fun z => whitneyVec (g z) i) ∘ φ'.symm) :=
    fun i => (h i).smooth φ' (tangentChart hφ (whitneyVec (g z) i)) hφ'
      (P.tangentPolyfold_isChart hφ _) V hVo hVsub fun y hy => whitneyVec_mem_tangentChartSet hy.2 i
  refine (IsScSmoothRetractMap.whitneyMk (φ'.isScRetract_image (fun y hy => (hVsub hy).2) hVo)
    φ.model.isScRetract hs₀ hs ?_).congr fun y _ => rfl
  rintro _ ⟨y, hy, rfl⟩ i
  change (tangentChartMap hφ (whitneyVec (g (φ'.symm (φ' y))) i)).1 =
    levelLift φ 1 (P.levelVal 1 (whitneyProj (g (φ'.symm (φ' y)))))
  rw [φ'.symm_apply_apply (hVsub hy).2]
  exact tangentChartMap_fst_of_mem_fiber hφ hy.2 (whitneyVec_mem_fiber _ i)

/-- The global form of `isScSmoothOn_whitneyLift`. -/
theorem isScSmoothMap_whitneyLift {g : Z → P.WhitneySum k}
    (h₀ : Q.IsScSmoothMap P.shift (fun z => whitneyProj (g z)))
    (h : ∀ i, Q.IsScSmoothMap P.tangentPolyfold (fun z => whitneyVec (g z) i)) :
    Q.IsScSmoothMap (P.whitneyPolyfold k) g :=
  isScSmoothOn_whitneyLift h₀ h

/-- **The converse**: a map into `⊕ₖ TX` is sc-smooth iff its base and its vectors are. -/
theorem isScSmoothOn_whitney_iff {g : Z → P.WhitneySum k} {U : Set Z} :
    Q.IsScSmoothOn (P.whitneyPolyfold k) g U ↔
      Q.IsScSmoothOn P.shift (fun z => whitneyProj (g z)) U ∧
        ∀ i, Q.IsScSmoothOn P.tangentPolyfold (fun z => whitneyVec (g z) i) U := by
  constructor
  · intro hg
    exact ⟨IsScSmoothOn.comp (g := whitneyProj (P := P) (k := k)) (U' := univ)
      isScSmoothMap_whitneyProj hg (mapsTo_univ _ _),
      fun i => IsScSmoothOn.comp (g := fun v : P.WhitneySum k => whitneyVec v i) (U' := univ)
        (isScSmoothMap_whitneyVec i) hg (mapsTo_univ _ _)⟩
  · rintro ⟨h₀, h⟩
    exact isScSmoothOn_whitneyLift h₀ h

end Lift


variable [ParacompactSpace (P.Level 1)] in
/-- **The Whitney sum `⊕ₖ TX → X¹` is an sc-smooth M-polyfold bundle** (2021 p. 195, "an easy
exercise", in the form of Theorem 2.3.16 for `TX → X¹`): `⊕ₖ TX` is an M-polyfold with the charts
`⊕ₖ Tφ` of the charts `φ` of `X`; `p : ⊕ₖ TX → X¹` is sc-smooth; in a chart `⊕ₖ Tφ`, `p` is the
first projection onto the level chart `φ¹` of `X¹`; the models `(⊕ₖ TO, C¹ ⊕ Eᵏ, E¹ ⊕ Eᵏ)` are
bundle retracts (`⊕ₖ Tr` covers `r¹`); and the transition maps of the charts are bundle maps
covering the transition maps of the charts `φ¹`, with linear fibre maps. -/
theorem whitneySum_bundle :
    (∀ {φ : MChart X} (hφ : P.IsChart φ) (v₀ : P.WhitneySum k),
      (P.whitneyPolyfold k).IsChart (whitneyChart hφ v₀)) ∧
    (P.whitneyPolyfold k).IsScSmoothMap P.shift (whitneyProj (P := P) (k := k)) ∧
    (∀ {φ : MChart X} (hφ : P.IsChart φ) (v₀ : P.WhitneySum k) (x₀ : P.Level 1)
      (v : P.WhitneySum k), (whitneyChart hφ v₀ v).1 = levelChart hφ x₀ (whitneyProj v)) ∧
    (∀ (φ : MChart X) (R : ScRetraction φ.model.E φ.model.C), R.retract = φ.model.O →
      ScRetraction.IsBundleRetractionOver (E := φ.model.E.shift) (F := φ.model.E.fiberPow k)
        (R.whitney k) R.shift) ∧
    (∀ {φ ψ : MChart X} (hφ : P.IsChart φ) (hψ : P.IsChart ψ) (v₀ w₀ : P.WhitneySum k),
      IsBundleMapOn (E := φ.model.E.shift) (F := φ.model.E.fiberPow k)
        (E' := ψ.model.E.shift) (F' := ψ.model.E.fiberPow k)
        ((whitneyChart hφ v₀).transition (whitneyChart hψ w₀))
        (retractWhitney φ.model.E φ.model.C (φ.overlap ψ) k) (levelMap (φ.transition ψ) 1)) := by
  refine ⟨fun hφ v₀ => whitneyPolyfold_isChart hφ v₀, isScSmoothMap_whitneyProj,
    fun hφ v₀ x₀ v => rfl, fun φ R _ => R.whitney_isBundleRetractionOver k,
    fun {φ ψ} hφ hψ v₀ w₀ => ?_⟩
  obtain ⟨ρ, hρ⟩ := ((hφ.compatible hψ (P := P)).1).retractTangentMap_isBundleMapOn
    (φ.isScRetract_overlap ψ)
  refine ⟨fun y => fiberPowMap k (ρ y), fun q hq => ?_⟩
  rw [whitneyChart_transition hφ v₀ hψ w₀ hq, retractWhitneyMap]
  refine Prod.ext rfl ?_
  conv_rhs => rw [← whitneyMk_fst_vec q]
  rw [fiberPowMap_apply]
  refine congrArg (ψ.model.E.fiberPackL 0 k) (funext fun i => ?_)
  rw [hρ _ (hq.2 i)]

/-! ### The fibres `p⁻¹(x) ≅ (T_xX)ᵏ` -/

section Fibre

variable (x : P.Level 1)

variable (k) in
/-- The fibre `p⁻¹(x)` of `⊕ₖ TX → X¹`. -/
def whitneyFiber : Set (P.WhitneySum k) := {v | whitneyProj v = x}

/-- **The fibre over `x` is `(T_xX)ᵏ`**: `(x, α₁, …, α_k) ↦ (α₁, …, α_k)`. -/
def whitneyFiberEquiv : whitneyFiber k x ≃ (Fin k → P.tangentFiber x) where
  toFun v i := ⟨whitneyVec v.1 i, by
    change P.tangentProj _ = x; rw [tangentProj_whitneyVec]; exact v.2⟩
  invFun α := ⟨whitneyMk x (fun i => (α i).1) fun i => (α i).2, rfl⟩
  left_inv v := by
    refine Subtype.ext (whitneySum_ext ?_ fun i => rfl)
    exact v.2.symm
  right_inv α := rfl

/-- The fibre `p⁻¹(x)` with the linear structure of `(T_xX)ᵏ` (Definition 2.3.14). -/
instance : AddCommGroup (whitneyFiber k x) := (whitneyFiberEquiv x).addCommGroup

instance : Module ℝ (whitneyFiber k x) := (whitneyFiberEquiv x).module ℝ

/-- `p⁻¹(x) ≃ₗ (T_xX)ᵏ`. -/
def whitneyFiberLinearEquiv : whitneyFiber k x ≃ₗ[ℝ] (Fin k → P.tangentFiber x) :=
  (whitneyFiberEquiv x).linearEquiv ℝ

variable {x} {φ : MChart X}

/-- **In a chart the fibre map is linear**: for `x ∈ V¹` and `v ∈ p⁻¹(x)`,
`⊕ₖ Tφ(v) = (φ(x), Tφ α₁, …, Tφ α_k)`, the linear isomorphism `(T_xX)ᵏ ≅ (T_{φ(x)}O)ᵏ` of
Definition 2.3.14 on each factor. -/
theorem whitneyChartMap_fiber (hφ : P.IsChart φ) (hx : P.levelVal 1 x ∈ φ.source)
    (v : whitneyFiber k x) :
    whitneyChartMap hφ v.1 = ScBanach.whitneyMk (levelLift φ 1 (P.levelVal 1 x))
      (fun i => (tangentFiberContinuousLinearEquiv hφ hx (whitneyFiberEquiv x v i) :
        φ.model.E 0)) := by
  have hv : whitneyProj v.1 = x := v.2
  refine Prod.ext (by rw [whitneyChartMap_fst, hv]) rfl

end Fibre

/-! ### The Whitney sum of an sc-smooth map, and functoriality -/

section Functor

universe v w

variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {S : MPolyfold Z}

/-- **`⊕ₖ Tf : ⊕ₖ TX → ⊕ₖ TY`**, `(x, α₁, …, α_k) ↦ (f(x), Tf α₁, …, Tf α_k)`, for an sc-smooth
`f : X → Y`. -/
def whitneyMapOf {f : X → Y} (hf : P.IsScSmoothMap Q f) (v : P.WhitneySum k) : Q.WhitneySum k :=
  whitneyMk (Q.levelMk 1 (f (P.levelVal 1 (whitneyProj v)))
      (hf.mapsTo_levelSet 1 (P.levelVal_mem _)))
    (fun i => tangentMap hf (whitneyVec v i)) fun i => level_ext (by
      rw [levelVal_tangentProj_tangentMap, tangentProj_whitneyVec, levelVal_levelMk])

variable {f : X → Y} (hf : P.IsScSmoothMap Q f)

@[simp] lemma levelVal_whitneyProj_whitneyMapOf (v : P.WhitneySum k) :
    Q.levelVal 1 (whitneyProj (whitneyMapOf hf v)) = f (P.levelVal 1 (whitneyProj v)) := rfl

@[simp] lemma whitneyVec_whitneyMapOf (v : P.WhitneySum k) (i : Fin k) :
    whitneyVec (whitneyMapOf hf v) i = tangentMap hf (whitneyVec v i) := rfl

/-- **`⊕ₖ Tf` is sc-smooth**: its base `f¹ ∘ p` and its vectors `Tf ∘ prᵢ` are. -/
theorem isScSmoothMap_whitneyMapOf :
    (P.whitneyPolyfold k).IsScSmoothMap (Q.whitneyPolyfold k) (whitneyMapOf (k := k) hf) := by
  refine isScSmoothMap_whitneyLift ?_ fun i => ?_
  · exact IsScSmoothOn.comp (U' := univ)
      (g := fun x => Q.levelMk 1 (f (P.levelVal 1 x)) (hf.mapsTo_levelSet 1 (P.levelVal_mem _)))
      (IsScSmoothMap.levelOne hf fun _ => rfl) isScSmoothMap_whitneyProj (mapsTo_univ _ _)
  · exact IsScSmoothOn.comp (U' := univ) (g := tangentMap hf) (tangentMap_isScSmooth hf)
      (isScSmoothMap_whitneyVec i) (mapsTo_univ _ _)

/-- `⊕ₖ T(id) = id`. -/
theorem whitneyMapOf_id : whitneyMapOf (P := P) (k := k) isScSmoothMap_id = id := by
  funext v
  refine whitneySum_ext rfl fun i => ?_
  rw [whitneyVec_whitneyMapOf, tangentMap_id]
  rfl

/-- **`⊕ₖ T(g ∘ f) = ⊕ₖ Tg ∘ ⊕ₖ Tf`** (the chain rule on each factor). -/
theorem whitneyMapOf_comp {g : Y → Z} (hg : Q.IsScSmoothMap S g) :
    whitneyMapOf (k := k) (hg.comp hf) = whitneyMapOf hg ∘ whitneyMapOf (k := k) hf := by
  funext v
  refine whitneySum_ext rfl fun i => ?_
  rw [whitneyVec_whitneyMapOf, tangentMap_comp hg hf]
  rfl

/-- `p ∘ ⊕ₖ Tf = f¹ ∘ p`. -/
theorem whitneyProj_whitneyMapOf (v : P.WhitneySum k) :
    whitneyProj (whitneyMapOf hf v) =
      Q.levelMk 1 (f (P.levelVal 1 (whitneyProj v))) (hf.mapsTo_levelSet 1 (P.levelVal_mem _)) :=
  rfl

end Functor

/-! ### `⊕₀ TX = X¹` and `⊕₁ TX = TX` -/

/-- `⊕₁ TX ≃ₜ TX`. -/
def whitneyOneHomeomorph : P.WhitneySum 1 ≃ₜ P.TangentSpace where
  toFun v := whitneyVec v 0
  invFun α := whitneyMk (P.tangentProj α) (fun _ => α) fun _ => rfl
  left_inv v := whitneySum_ext (tangentProj_whitneyVec v 0) fun i => by
    rw [Subsingleton.elim i 0]; rfl
  right_inv _ := rfl
  continuous_toFun := continuous_whitneyVec 0
  continuous_invFun := by
    rw [← continuousOn_univ, continuousOn_whitney_iff]
    exact ⟨continuous_tangentProj.continuousOn, fun _ => continuousOn_id⟩

/-- `⊕₀ TX ≃ₜ X¹`. -/
def whitneyZeroHomeomorph : P.WhitneySum 0 ≃ₜ P.Level 1 where
  toFun := whitneyProj
  invFun x := whitneyMk x Fin.elim0 fun i => i.elim0
  left_inv v := whitneySum_ext rfl fun i => i.elim0
  right_inv _ := rfl
  continuous_toFun := continuous_whitneyProj
  continuous_invFun := by
    rw [← continuousOn_univ, continuousOn_whitney_iff]
    exact ⟨continuousOn_id, fun i => i.elim0⟩

end MPolyfold

end Polyfold
