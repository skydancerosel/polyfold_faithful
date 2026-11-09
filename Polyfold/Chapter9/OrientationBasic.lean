import Polyfold.Chapter9.OrientationTangent

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.3 "Orientations": **Definition 9.3.2** (2021 p. 423; 2017: Definition
9.8) and **Remark 9.3.3** (2021 p. 423; 2017: Remark 9.8).  Numbers and pages are the 2021
text's, the 2017 ones in parentheses.

# Orientations of branched ep⁺-subgroupoids

## The text, paraphrased

(Definition 9.3.2) An orientation of a branched ep⁺-subgroupoid `Θ` is a section functor
`T̂_Θ : X_∞ → Gr̂(X)` lifting `T_Θ` (`T_Θ = f ∘ T̂_Θ`) such that every `x` with `Θ(x) > 0` has a
local representation with oriented `(Mᵢ, oᵢ)`, `T̂_Θ(y) = ∑ σᵢ · T_y(Mᵢ, oᵢ)` (9.9); it is an
oriented lift of `T_Θ`, and `Θ` is orientable if one exists.  (Remark 9.3.3) (9.9) means the
local continuity of `x ↦ T̂_Θ(x)` on `supp(Θ)`; an orientable `Θ` may have more than two
orientations, by its fractional nature.

## What is formalized

* `MPolyfold.SubmanifoldOrientation M n` (positive frames of `T_yM` at every `y ∈ M`, locally
  continuous in a chart) with `tangent` (`T_y(M, o)`), `restrict`, `ofPoint`; chart
  descriptions `chartVec_image_submanifoldTangent`, `exists_submodule_chartVec_image`,
  `exists_two_orientations_submanifoldTangent`.
* `EpGroupoid.OrientedBranchingStructure` and its sum `orientedSum` (9.9), with
  `grForget_orientedSum` (it lifts `∑ σᵢ T_yMᵢ`).
* **Definition 9.3.2**: `IsOrientation Θ T` (values in `Gr̂`, naturality, lifting, (9.9)) and
  `IsOrientable`; `IsOrientation.mk'` (the lifting condition from (9.9) under Theorem 9.2.1's
  independence `HasIndependentTangentSums`), the section functor `orientedSection` over `Gr̂(X)`
  with `orientedSection_comp_grHatProj` and `orientedSection_comp_grForgetFunctor_obj/_map`.
* Satisfiability: `isOrientation_zero`, and `isOrientation_sum_rn` (closed oriented submanifolds of
  `ℝⁿ`, given independence).
* **Remark 9.3.3**: `remark_9_3_3` (the indicator of a point of `ℝⁿ` has the orientations
  `q · (+) + (1 - q) · (-)`, `q ∈ (0, 1) ∩ ℚ`, pairwise different); the first sentence is built
  into the continuity field of `SubmanifoldOrientation`.

## What the text leaves implicit, and the choices made

* "Section functor": a natural family `T x ∈ Gr̂(x)` for smooth `x`; the oriented submanifolds of
  (9.9) carry their own dimensions `dᵢ`.
* Where the lift `T_Θ` needs Theorem 9.2.1, its independence is a hypothesis (`hind`).
-/

set_option maxSynthPendingDepth 3

open Set Module Submodule Filter Topology CategoryTheory

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
variable {φ : MChart X} (hφ : P.IsChart φ)

/-! ### The chart description of `T_yA` -/

/-- **The chart description of `T_yA`** (Remark 4.14 in a chart): for data `(V, s)` of
Definition 4.13 at `y ∈ A` and a chart `φ` at `y`, the chart vectors of `T_yA` form the tangent
space `T_z(φ(W ∩ A))` of the chart model of `A`. -/
theorem chartVec_image_submanifoldTangent {A : Set X} (d : P.SubmanifoldData A) {y : X}
    (hyA : y ∈ A) (hyV : y ∈ d.V) (hyφ : y ∈ φ.source) :
    chartVec hφ '' P.submanifoldTangent A y =
      tangentSpace φ.model.E φ.model.C (φ '' (d.toSubData.shrink φ ∩ A)) (levelLift φ 1 y) := by
  ext h
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact (d.tangentChartMap_of_mem_submanifoldTangent hφ hyA hyV hyφ hα).2
  · intro hh
    obtain ⟨α, hα, hαh⟩ := d.exists_mem_submanifoldTangent hφ hyA hyV hyφ hh
    exact ⟨α, hα, congrArg Prod.snd hαh⟩

/-- **The chart image of `T_yA` is an `n`-dimensional linear subspace** of `E₀` if `A` has
dimension `n` at `y`. -/
theorem exists_submodule_chartVec_image {A : Set X} (hA : P.IsSmoothSubmanifold A) {y : X}
    {n : ℕ} (h : P.HasDimAt A y n) (hyφ : y ∈ φ.source) :
    ∃ N : Submodule ℝ (φ.model.E 0),
      (N : Set (φ.model.E 0)) = chartVec hφ '' P.submanifoldTangent A y ∧
        FiniteDimensional ℝ N ∧ finrank ℝ N = n := by
  set d := hA.data h.1
  have hyV : y ∈ d.V := hA.mem_data_V h.1
  have hy1 : y ∈ P.levelSet 1 := d.mem_levelSet_one h.1 hyV
  have hz : φ.model.E.toBase 1 (levelLift φ 1 y) = φ y := P.toBase_levelLift hφ hyφ hy1
  obtain ⟨-, -, -, N, hN, hfin⟩ := d.remark_4_2_2 hφ h.1 hyV hyφ hz
  refine ⟨N, hN.trans (chartVec_image_submanifoldTangent hφ d h.1 hyV hyφ).symm, hfin, ?_⟩
  have hk := h.finrank_eq d hφ hyV hyφ hz
  rw [← hN, span_eq] at hk
  exact hk

/-- The chart image of `T_p{p}` is `{0}`. -/
theorem chartVec_image_submanifoldTangent_singleton {p : X} (hp : p ∈ P.smoothSet)
    (hpφ : p ∈ φ.source) : chartVec hφ '' P.submanifoldTangent {p} p = {0} := by
  have hA := isSmoothSubmanifold_singleton hp
  set d := hA.data (mem_singleton p)
  have hpV : p ∈ d.V := hA.mem_data_V (mem_singleton p)
  have hp1 : p ∈ P.levelSet 1 := hA.mem_levelSet_one (mem_singleton p)
  have hz : φ.model.E.toBase 1 (levelLift φ 1 p) = φ p := P.toBase_levelLift hφ hpφ hp1
  have hQ : φ '' (d.toSubData.shrink φ ∩ {p}) = {φ p} := by
    rw [inter_eq_right.2 (singleton_subset_iff.2
      (d.toSubData.mem_shrink φ (mem_singleton p) hpV hpφ)), image_singleton]
  obtain ⟨R, hR⟩ := d.toSubData.isScRetract_image φ hφ
  obtain ⟨-, -, -, N, hN, -⟩ := d.remark_4_2_2 hφ (mem_singleton p) hpV hpφ hz
  rw [chartVec_image_submanifoldTangent hφ d (mem_singleton p) hpV hpφ]
  refine Subset.antisymm (fun v hv => ?_) ?_
  · rw [hQ] at hv
    exact tangentSpace_singleton_subset R (hR.trans hQ) hz hv
  · rintro _ rfl
    rw [← hN]
    exact N.zero_mem

/-- **`T_yA` has exactly two orientations** for an `n`-dimensional submanifold `A ∋ y`. -/
theorem exists_two_orientations_submanifoldTangent {A : Set X} {n : ℕ}
    (hA : P.IsSubmanifoldOfDim A n) {y : X} (hy : y ∈ A) :
    ∃ O₁ O₂ : Set (Fin n → P.TangentSpace), O₁ ≠ O₂ ∧
      ∀ O, P.IsOrientedAt y ⟨n, P.submanifoldTangent A y, O⟩ ↔ O = O₁ ∨ O = O₂ := by
  obtain ⟨φ, hφ, hyφ⟩ := P.exists_isChart_mem_source y
  obtain ⟨N, hN, hfin, hn⟩ := exists_submodule_chartVec_image hφ hA.1 (hA.2 y hy) hyφ
  exact exists_two_orientations hφ hyφ (fun α hα => hα.1) hN hn

/-! ### Oriented submanifolds -/

variable (P) in
/-- **An orientation `o` of an `n`-dimensional submanifold `M`**: an orientation `o_y` of `T_yM`
at every `y ∈ M` (given by its positive frames), continuous in the usual sense: near every point
there are a chart `φ` and a frame field `y ↦ e(y)`, positive for `o`, whose chart vectors depend
continuously on `y`.  For `n = 0` there is no continuity condition (an orientation of a
`0`-dimensional manifold is a sign at each point; the negative one has no positive frame). -/
structure SubmanifoldOrientation (M : Set X) (n : ℕ) where
  /-- The positive frames of `T_yM`. -/
  frames : X → Set (Fin n → P.TangentSpace)
  isOrientedAt : ∀ y ∈ M, P.IsOrientedAt y ⟨n, P.submanifoldTangent M y, frames y⟩
  continuous : 0 < n → ∀ y ∈ M, ∃ (φ : MChart X) (hφ : P.IsChart φ) (V : Set X), IsOpen V ∧
    y ∈ V ∧ V ⊆ φ.source ∧ ∃ e : X → Fin n → P.TangentSpace, (∀ z ∈ M ∩ V, e z ∈ frames z) ∧
      ContinuousOn (fun z i => chartVec hφ (e z i)) (M ∩ V)

namespace SubmanifoldOrientation

variable {M : Set X} {n : ℕ} (o : P.SubmanifoldOrientation M n)

/-- **`T_y(M, o)`**, the oriented tangent space of `(M, o)` at `y`. -/
def tangent (y : X) : OrTangent P := ⟨n, P.submanifoldTangent M y, o.frames y⟩

@[simp] theorem tangent_dim (y : X) : (o.tangent y).dim = n := rfl

@[simp] theorem tangent_carrier (y : X) : (o.tangent y).carrier = P.submanifoldTangent M y := rfl

theorem isOrientedAt_tangent {y : X} (hy : y ∈ M) : P.IsOrientedAt y (o.tangent y) :=
  o.isOrientedAt y hy

/-- The restriction of an orientation to an open piece `M ∩ V'`. -/
def restrict {V' : Set X} (hV' : IsOpen V') : P.SubmanifoldOrientation (M ∩ V') n where
  frames := o.frames
  isOrientedAt y hy := by
    rw [submanifoldTangent_inter_isOpen hV' hy.2]
    exact o.isOrientedAt y hy.1
  continuous hn y hy := by
    obtain ⟨φ, hφ, V, hV, hyV, hVφ, e, he, hc⟩ := o.continuous hn y hy.1
    exact ⟨φ, hφ, V, hV, hyV, hVφ, e, fun z hz => he z ⟨hz.1.1, hz.2⟩,
      hc.mono fun z hz => ⟨hz.1.1, hz.2⟩⟩

theorem restrict_tangent {V' : Set X} (hV' : IsOpen V') {y : X} (hy : y ∈ V') :
    (o.restrict hV').tangent y = o.tangent y := by
  simp only [tangent, restrict, submanifoldTangent_inter_isOpen hV' hy]

end SubmanifoldOrientation

/-- **The two orientations of a smooth point** `{p}` (`n = 0`): any set of (empty) frames that
orients `T_p{p}` is an orientation of the `0`-dimensional submanifold `{p}`. -/
def SubmanifoldOrientation.ofPoint {p : X} (O : Set (Fin 0 → P.TangentSpace))
    (hO : P.IsOrientedAt p ⟨0, P.submanifoldTangent {p} p, O⟩) :
    P.SubmanifoldOrientation {p} 0 where
  frames _ := O
  isOrientedAt y hy := by rw [mem_singleton_iff.1 hy]; exact hO
  continuous hn := (lt_irrefl 0 hn).elim

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-! ### Oriented local branching structures -/

variable (X) in
/-- **A local branching structure with orientations** `(Mᵢ, oᵢ)_{i ∈ I}`, `(σᵢ)_{i ∈ I}`
(2021 p. 423): a local branching structure whose submanifolds `Mᵢ` are `dᵢ`-dimensional and
oriented. -/
structure OrientedBranchingStructure (Θ : Obj → ℚ) (x : Obj) extends
    X.LocalBranchingStructure Θ x where
  /-- The dimensions `dᵢ = dim Mᵢ`. -/
  dim : ι → ℕ
  isSubmanifoldOfDim : ∀ i, X.PObj.IsSubmanifoldOfDim (M i) (dim i)
  /-- The orientations `oᵢ`. -/
  orient : ∀ i, X.PObj.SubmanifoldOrientation (M i) (dim i)

namespace OrientedBranchingStructure

variable {Θ : Obj → ℚ} {x : Obj} (B : X.OrientedBranchingStructure Θ x)

open scoped Classical in
/-- **`∑_{i ∈ I, y ∈ Mᵢ} σᵢ · T_y(Mᵢ, oᵢ)`**, the right-hand side of (9.9). -/
def orientedSum (y : Obj) : X.PObj.OrTangent →₀ ℚ :=
  ∑ i with y ∈ B.M i, Finsupp.single ((B.orient i).tangent y) (B.σ i)

open scoped Classical in
theorem orientedSum_apply (y : Obj) (g : X.PObj.OrTangent) :
    B.orientedSum y g = ∑ i with y ∈ B.M i, if (B.orient i).tangent y = g then B.σ i else 0 := by
  rw [orientedSum, Finsupp.finsetSum_apply]
  exact Finset.sum_congr rfl fun i _ => Finsupp.single_apply

theorem orientedSum_mem (y : Obj) : B.orientedSum y ∈ X.GrHat y := by
  classical
  refine ⟨fun g => ?_, fun g hg => ?_⟩
  · rw [B.orientedSum_apply]
    exact Finset.sum_nonneg fun i _ => by split_ifs; exacts [(B.σ_pos i).le, le_rfl]
  · have : ∃ i, y ∈ B.M i ∧ (B.orient i).tangent y = g := by
      by_contra h
      push Not at h
      exact (Finsupp.mem_support_iff.1 hg) (by
        rw [B.orientedSum_apply]
        exact Finset.sum_eq_zero fun i hi => if_neg (h i (Finset.mem_filter.1 hi).2))
    obtain ⟨i, hyi, rfl⟩ := this
    exact (B.orient i).isOrientedAt_tangent hyi

open scoped Classical in
/-- `f(∑ σᵢ · T_y(Mᵢ, oᵢ)) = ∑ σᵢ · T_yMᵢ`. -/
theorem grForget_orientedSum (y : Obj) :
    X.grForget (B.orientedSum y) =
      ∑ i with y ∈ B.M i, Finsupp.single (X.PObj.submanifoldTangent (B.M i) y) (B.σ i) := by
  rw [orientedSum, grForget, Finsupp.mapDomain_finsetSum]
  exact Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_single

/-- **At `x` the forgetful map gives `∑ σᵢ · T_xMᵢ`** (all `Mᵢ` contain `x`). -/
theorem grForget_orientedSum_self : X.grForget (B.orientedSum x) = B.tangentSum := by
  classical
  rw [grForget_orientedSum, LocalBranchingStructure.tangentSum,
    Finset.filter_true_of_mem fun i _ => B.mem_M i]

end OrientedBranchingStructure

/-! ### Definition 9.3.2 -/

variable (X) in
/-- **Definition 9.3.2 (orientation), 2021 p. 423 (2017: Definition 9.8)**: an orientation of the
branched ep⁺-subgroupoid `Θ` is a section `T̂Θ : X_∞ → Gr̂(X)` (`T̂Θ(x) ∈ Gr̂(x)`, natural:
`t(T̂Θ(s φ), φ) = T̂Θ(t φ)`) lifting `TΘ` (`f ∘ T̂Θ = TΘ`) such that at every `x` with `Θ(x) > 0`
there is a local representation with orientations, `T̂Θ(y) = ∑ σᵢ · T_y(Mᵢ, oᵢ)` on `U(x)`
(9.9).  `T̂Θ` is an **oriented lift** of `TΘ`; the section functor is `orientedSection`. -/
structure IsOrientation (Θ : Obj → ℚ) (T : Obj → X.PObj.OrTangent →₀ ℚ) : Prop where
  mem : ∀ x ∈ X.PObj.smoothSet, T x ∈ X.GrHat x
  natural : ∀ φ : Mor, X.src φ ∈ X.PObj.smoothSet → X.grHatPush φ (T (X.src φ)) = T (X.tgt φ)
  lifts : ∀ x ∈ X.PObj.smoothSet, X.grForget (T x) = X.tangentValue Θ x
  locallyOriented : ∀ x ∈ supp Θ, ∃ B : X.OrientedBranchingStructure Θ x,
    ∀ y ∈ B.U, y ∈ X.PObj.smoothSet → T y = B.orientedSum y

variable (X) in
/-- **Definition 9.3.2 (orientable)**: `TΘ` admits an oriented lift. -/
def IsOrientable (Θ : Obj → ℚ) : Prop := ∃ T, X.IsOrientation Θ T

variable {Θ : Obj → ℚ} {T : Obj → X.PObj.OrTangent →₀ ℚ}

/-- An oriented lift vanishes off `supp(Θ)` (its image `TΘ(x)` is the zero-sum there). -/
theorem IsOrientation.eq_zero_of_not_mem (hT : X.IsOrientation Θ T) {x : Obj}
    (hx : x ∈ X.PObj.smoothSet) (hxs : x ∉ supp Θ) : T x = 0 :=
  eq_zero_of_grForget_eq_zero (hT.mem x hx).1
    ((hT.lifts x hx).trans (X.tangentValue_eq_zero hxs))

/-- **The lifting condition follows from (9.9)** once Theorem 9.2.1's independence holds: a
natural section of `Gr̂(X)`, zero off `supp(Θ)` and locally of the form (9.9), is an
orientation. -/
theorem IsOrientation.mk' (hind : X.HasIndependentTangentSums Θ)
    (hmem : ∀ x ∈ X.PObj.smoothSet, T x ∈ X.GrHat x)
    (hnat : ∀ φ : Mor, X.src φ ∈ X.PObj.smoothSet → X.grHatPush φ (T (X.src φ)) = T (X.tgt φ))
    (hzero : ∀ x ∈ X.PObj.smoothSet, x ∉ supp Θ → T x = 0)
    (hloc : ∀ x ∈ supp Θ, ∃ B : X.OrientedBranchingStructure Θ x,
      ∀ y ∈ B.U, y ∈ X.PObj.smoothSet → T y = B.orientedSum y) :
    X.IsOrientation Θ T where
  mem := hmem
  natural := hnat
  lifts x hx := by
    by_cases hxs : x ∈ supp Θ
    · obtain ⟨B, hB⟩ := hloc x hxs
      rw [hB x B.mem_U hx, B.grForget_orientedSum_self,
        X.tangentValue_eq hind B.toLocalBranchingStructure]
    · rw [hzero x hx hxs, X.tangentValue_eq_zero hxs, grForget, Finsupp.mapDomain_zero]
  locallyOriented := hloc

variable (X) in
/-- **The oriented lift as a section functor `T̂Θ : X_∞ → Gr̂(X)`**: `x ↦ T̂Θ(x)`,
`φ ↦ (T̂Θ(s φ), φ)`. -/
def orientedSection (hT : X.IsOrientation Θ T) : X.SmoothCat ⥤ X.GrHatObj where
  obj x := ⟨x.pt, x.smooth, T x.pt, hT.mem _ x.smooth⟩
  map {x y} f := ⟨SmoothCat.mor f, SmoothCat.src_mor f, SmoothCat.tgt_mor f, by
    change X.grHatPush (SmoothCat.mor f) (T x.pt) = T y.pt
    rw [← SmoothCat.src_mor f, ← SmoothCat.tgt_mor f]
    exact hT.natural _ (by rw [SmoothCat.src_mor f]; exact x.smooth)⟩
  map_id x := Subtype.ext (SmoothCat.mor_id x)
  map_comp f g := Subtype.ext (SmoothCat.mor_comp f g)

/-- `π̂ ∘ T̂Θ = Id_{X_∞}`: `T̂Θ` is a section. -/
theorem orientedSection_comp_grHatProj (hT : X.IsOrientation Θ T) :
    X.orientedSection hT ⋙ X.grHatProj = 𝟭 X.SmoothCat := rfl

/-- **`TΘ = f ∘ T̂Θ`** (Definition 9.3.2), on objects. -/
theorem orientedSection_comp_grForgetFunctor_obj (hT : X.IsOrientation Θ T)
    (hΘ : X.IsBranchedEpSubgroupoid Θ) (hind : X.HasIndependentTangentSums Θ)
    (x : X.SmoothCat) :
    (X.orientedSection hT ⋙ X.grForgetFunctor).obj x = (X.tangentSection hΘ hind).obj x := by
  change (⟨x.pt, x.smooth, X.grForget (T x.pt), _⟩ : X.GrObj) =
    ⟨x.pt, x.smooth, X.tangentValue Θ x.pt, _⟩
  congr 1
  exact hT.lifts _ x.smooth

/-- **`TΘ = f ∘ T̂Θ`** (Definition 9.3.2), on morphisms. -/
theorem orientedSection_comp_grForgetFunctor_map (hT : X.IsOrientation Θ T)
    (hΘ : X.IsBranchedEpSubgroupoid Θ) (hind : X.HasIndependentTangentSums Θ)
    {x y : X.SmoothCat} (f : x ⟶ y) :
    ((X.orientedSection hT ⋙ X.grForgetFunctor).map f).1 =
      ((X.tangentSection hΘ hind).map f).1 := rfl

/-- **Satisfiability: `Θ = 0` is oriented by `T̂Θ = 0`.** -/
theorem isOrientation_zero : X.IsOrientation 0 fun _ => 0 where
  mem x _ := X.zero_mem_GrHat x
  natural φ _ := by rw [grHatPush, Finsupp.mapDomain_zero]
  lifts x _ := by
    rw [grForget, Finsupp.mapDomain_zero,
      X.tangentValue_eq_zero (fun h => lt_irrefl (0 : ℚ) h)]
  locallyOriented x hx := (lt_irrefl (0 : ℚ) hx).elim

theorem isOrientable_zero : X.IsOrientable 0 := ⟨_, isOrientation_zero⟩

/-! ### Oriented sums of closed oriented submanifolds of `ℝⁿ` -/

section TrivialRn

variable {n : ℕ}

open scoped Classical in
/-- `T̂(y) = ∑_{i : y ∈ Mᵢ} σᵢ · T_y(Mᵢ, oᵢ)` for finitely many oriented submanifolds
`(Mᵢ, oᵢ)` of `ℝⁿ` and weights `σᵢ`. -/
def orientedSumRn {ι : Type} [Fintype ι] (M : ι → Set (Fin n → ℝ)) (σ : ι → ℚ)
    {dim : ι → ℕ} (o : ∀ i, (rnPolyfold n).SubmanifoldOrientation (M i) (dim i))
    (y : Fin n → ℝ) : (rnPolyfold n).OrTangent →₀ ℚ :=
  ∑ i with y ∈ M i, Finsupp.single ((o i).tangent y) (σ i)

open scoped Classical in
/-- **The oriented local branching structure of `∑ σᵢ 1_{Mᵢ}`** at `x`, for closed oriented
submanifolds `(Mᵢ, oᵢ)` of `ℝⁿ` (`localBranchingStructure_sum_rn` with the restricted
orientations). -/
def orientedBranchingStructure_sum_rn {ι : Type} [Fintype ι] (M : ι → Set (Fin n → ℝ))
    (σ : ι → ℚ) (hσ : ∀ i, 0 < σ i) {dim : ι → ℕ}
    (hM : ∀ i, (rnPolyfold n).IsSubmanifoldOfDim (M i) (dim i)) (hc : ∀ i, IsClosed (M i))
    (o : ∀ i, (rnPolyfold n).SubmanifoldOrientation (M i) (dim i)) (x : Fin n → ℝ) :
    (trivial (rnPolyfold n)).OrientedBranchingStructure (fun y => ∑ i with y ∈ M i, σ i) x where
  toLocalBranchingStructure := localBranchingStructure_sum_rn M σ hσ (fun i => (hM i).1) hc x
  dim i := dim i.1
  isSubmanifoldOfDim i := (hM i.1).inter_isOpen
    (localBranchingStructure_sum_rn M σ hσ (fun i => (hM i).1) hc x).isOpen_U
  orient i := (o i.1).restrict
    (localBranchingStructure_sum_rn M σ hσ (fun i => (hM i).1) hc x).isOpen_U

open scoped Classical in
/-- On `U(x)`, the oriented sum of the structure at `x` is `T̂(y) = ∑_{y ∈ Mᵢ} σᵢ T_y(Mᵢ, oᵢ)`. -/
theorem orientedSum_sum_rn_eq {ι : Type} [Fintype ι] (M : ι → Set (Fin n → ℝ))
    (σ : ι → ℚ) (hσ : ∀ i, 0 < σ i) {dim : ι → ℕ}
    (hM : ∀ i, (rnPolyfold n).IsSubmanifoldOfDim (M i) (dim i)) (hc : ∀ i, IsClosed (M i))
    (o : ∀ i, (rnPolyfold n).SubmanifoldOrientation (M i) (dim i)) {x y : Fin n → ℝ}
    (hy : y ∈ (orientedBranchingStructure_sum_rn M σ hσ hM hc o x).U) :
    (orientedBranchingStructure_sum_rn M σ hσ hM hc o x).orientedSum y = orientedSumRn M σ o y := by
  have hU : ∀ i, y ∈ M i → x ∈ M i := hy
  have hUo : IsOpen (orientedBranchingStructure_sum_rn M σ hσ hM hc o x).U :=
    (orientedBranchingStructure_sum_rn M σ hσ hM hc o x).isOpen_U
  rw [OrientedBranchingStructure.orientedSum, orientedSumRn, Finset.sum_filter, Finset.sum_filter]
  have h1 : (∑ i, if y ∈ M i then Finsupp.single ((o i).tangent y) (σ i) else 0) =
      ∑ i ∈ Finset.univ.filter (fun i => x ∈ M i),
        (if y ∈ M i then Finsupp.single ((o i).tangent y) (σ i) else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hyi : y ∈ M i
    · simp [hyi, hU i hyi]
    · simp [hyi]
  rw [h1, Finset.sum_subtype (Finset.univ.filter fun i => x ∈ M i) (p := fun i => x ∈ M i)
    (by simp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hyi : y ∈ M i.1
  · rw [if_pos (show y ∈ (orientedBranchingStructure_sum_rn M σ hσ hM hc o x).M i from
      ⟨hyi, hy⟩), if_pos hyi]
    exact congrArg (fun g => Finsupp.single g (σ i.1))
      (MPolyfold.SubmanifoldOrientation.restrict_tangent _ hUo hy)
  · rw [if_neg (show y ∉ (orientedBranchingStructure_sum_rn M σ hσ hM hc o x).M i from
      fun h => hyi h.1), if_neg hyi]
    rfl

open scoped Classical in
/-- **Satisfiability of Definition 9.3.2 with nonzero data**: for finitely many closed oriented
submanifolds `(Mᵢ, oᵢ)` of `ℝⁿ` and weights `σᵢ > 0`, `T̂(y) = ∑_{y ∈ Mᵢ} σᵢ · T_y(Mᵢ, oᵢ)` is an
orientation of `Θ = ∑ σᵢ 1_{Mᵢ}`, given Theorem 9.2.1's independence for `Θ`. -/
theorem isOrientation_sum_rn {ι : Type} [Fintype ι] (M : ι → Set (Fin n → ℝ))
    (σ : ι → ℚ) (hσ : ∀ i, 0 < σ i) {dim : ι → ℕ}
    (hM : ∀ i, (rnPolyfold n).IsSubmanifoldOfDim (M i) (dim i)) (hc : ∀ i, IsClosed (M i))
    (o : ∀ i, (rnPolyfold n).SubmanifoldOrientation (M i) (dim i))
    (hind : (trivial (rnPolyfold n)).HasIndependentTangentSums
      (fun y => ∑ i with y ∈ M i, σ i)) :
    (trivial (rnPolyfold n)).IsOrientation (fun y => ∑ i with y ∈ M i, σ i)
      (orientedSumRn M σ o) := by
  have hmem : ∀ y, orientedSumRn M σ o y ∈ (trivial (rnPolyfold n)).GrHat y := fun y => by
    rw [← orientedSum_sum_rn_eq M σ hσ hM hc o
      (orientedBranchingStructure_sum_rn M σ hσ hM hc o y).mem_U]
    exact OrientedBranchingStructure.orientedSum_mem _ y
  refine IsOrientation.mk' hind (fun y _ => hmem y) (fun φ _ => grHatPush_unit (hmem φ))
    (fun y _ hy => ?_) (fun x _ => ⟨orientedBranchingStructure_sum_rn M σ hσ hM hc o x,
      fun y hy _ => (orientedSum_sum_rn_eq M σ hσ hM hc o hy).symm⟩)
  refine Finset.sum_eq_zero fun i hi => (hy ?_).elim
  exact Finset.sum_pos' (fun j _ => (hσ j).le) ⟨i, hi, hσ i⟩

open scoped Classical in
/-- `isOrientation_sum_rn` for any functor `Θ` equal to `∑ σᵢ 1_{Mᵢ}`. -/
theorem isOrientation_sum_rn' {ι : Type} [Fintype ι] (M : ι → Set (Fin n → ℝ))
    (σ : ι → ℚ) (hσ : ∀ i, 0 < σ i) {dim : ι → ℕ}
    (hM : ∀ i, (rnPolyfold n).IsSubmanifoldOfDim (M i) (dim i)) (hc : ∀ i, IsClosed (M i))
    (o : ∀ i, (rnPolyfold n).SubmanifoldOrientation (M i) (dim i)) {Θ : (Fin n → ℝ) → ℚ}
    (hΘ : Θ = fun y => ∑ i with y ∈ M i, σ i)
    (hind : (trivial (rnPolyfold n)).HasIndependentTangentSums Θ) :
    (trivial (rnPolyfold n)).IsOrientation Θ (orientedSumRn M σ o) := by
  subst hΘ
  exact isOrientation_sum_rn M σ hσ hM hc o hind

/-! ### Remark 9.3.3: more than two orientations -/

/-- The weights `q`, `1 - q` on `Bool`. -/
def boolWeight (q : ℚ) (b : Bool) : ℚ := if b then q else 1 - q

/-- The two orientations `O₁ ≠ O₂` of `T_p{p}` for a point `p` of `ℝⁿ`. -/
theorem exists_two_orientations_point (p : Fin n → ℝ) :
    ∃ O₁ O₂ : Set (Fin 0 → (rnPolyfold n).TangentSpace), O₁ ≠ O₂ ∧
      (rnPolyfold n).IsOrientedAt p ⟨0, (rnPolyfold n).submanifoldTangent {p} p, O₁⟩ ∧
      (rnPolyfold n).IsOrientedAt p ⟨0, (rnPolyfold n).submanifoldTangent {p} p, O₂⟩ := by
  obtain ⟨O₁, O₂, hne, hO⟩ := MPolyfold.exists_two_orientations_submanifoldTangent
    (rnPolyfold_isSubmanifoldOfDim_singleton p) (mem_singleton p)
  exact ⟨O₁, O₂, hne, (hO O₁).2 (Or.inl rfl), (hO O₂).2 (Or.inr rfl)⟩

/-- **Remark 9.3.3, 2021 p. 423 (2017: Remark 9.8)**: an orientable `Θ` "might allow more than two
possible orientations due to its 'fractional nature'".  For the indicator `Θ = 1_{p}` of a point
of `ℝⁿ` and the two orientations `±` of `T_p{p}`, every `q ∈ (0, 1) ∩ ℚ` gives the orientation
`T̂_q(p) = q · (T_p{p}, +) + (1 - q) · (T_p{p}, -)` (the local branching structure `{p}, {p}` with
weights `q`, `1 - q`), and `q ↦ T̂_q` is injective: `Θ` has infinitely many orientations. -/
theorem remark_9_3_3 (p : Fin n → ℝ) :
    ∃ T : ℚ → (Fin n → ℝ) → (rnPolyfold n).OrTangent →₀ ℚ,
      (∀ q, 0 < q → q < 1 →
        (trivial (rnPolyfold n)).IsOrientation (({p} : Set (Fin n → ℝ)).indicator 1) (T q)) ∧
      ∀ q q', T q = T q' → q = q' := by
  classical
  obtain ⟨O₁, O₂, hne, h₁, h₂⟩ := exists_two_orientations_point p
  let o : ∀ b : Bool, (rnPolyfold n).SubmanifoldOrientation {p} 0 := fun b =>
    Bool.rec (MPolyfold.SubmanifoldOrientation.ofPoint O₂ h₂)
      (MPolyfold.SubmanifoldOrientation.ofPoint O₁ h₁) b
  have hd : ∀ _ : Bool, (rnPolyfold n).IsSubmanifoldOfDim {p} 0 := fun _ =>
    rnPolyfold_isSubmanifoldOfDim_singleton p
  refine ⟨fun q => orientedSumRn (fun _ : Bool => ({p} : Set (Fin n → ℝ))) (boolWeight q)
    (dim := fun _ => 0) o, fun q hq hq1 => ?_, fun q q' h => ?_⟩
  · have hσ : ∀ b, 0 < boolWeight q b := fun b => by
      cases b
      · simp [boolWeight]; linarith
      · simpa [boolWeight] using hq
    refine isOrientation_sum_rn' (fun _ : Bool => ({p} : Set (Fin n → ℝ))) (boolWeight q) hσ hd
      (fun _ => isClosed_singleton) o ?_ (hasIndependentTangentSums_indicator n p)
    funext y
    by_cases hy : y = p
    · subst hy; simp [boolWeight]
    · simp [hy]
  · have hg : ((o true).tangent p) ≠ ((o false).tangent p) := by
      intro h'
      apply hne
      change (⟨0, (rnPolyfold n).submanifoldTangent {p} p, O₁⟩ : (rnPolyfold n).OrTangent) =
        ⟨0, (rnPolyfold n).submanifoldTangent {p} p, O₂⟩ at h'
      simpa using h'
    have h1 := congrFun (congrArg DFunLike.coe (congrFun h p)) ((o true).tangent p)
    simpa [orientedSumRn, boolWeight, hg] using h1

end TrivialRn

end EpGroupoid

end Polyfold
