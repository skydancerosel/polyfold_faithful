import GWMemoir.Skeleton
import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# The exponential map of good data, read as a local addition (Memoir Definition 3.6 (3))

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, Definition 3.6 (2)–(4),
p. 65, and §2.5, p. 52.

Definition 3.6 (3) takes the exponential map of a Riemannian metric `g` on `Q` which over the sets
`R₄(w) = ψ_w⁻¹(B₄(0))` is the pull-back of the Euclidean metric by the charts `ψ_w` of (2), and an
open neighbourhood `O` of the zero section, fibrewise convex, on whose fibres `exp_q` is an
embedding.  The proofs use of `exp`: that it is smooth, `exp_q(0) = q`, `d exp_q(0) = id`, the
embedding property, and the formula `ψ(exp_p V) = ψ(p) + Tψ(p) V` for `p ∈ R₂(w)`, `|V|_p ≤ 2`
(p. 52, which gives Proposition 2.51).  Mathlib has Riemannian metrics and the Riemannian distance
but no geodesics.  We therefore read Definition 3.6 (3) as follows.

* `LocalAddition E Q`: an open, fibrewise convex neighbourhood `O` of the zero section of `TQ` and
  a map `ex : TQ → Q`, smooth on `O`, with `ex(q, 0) = q`, `d(ex_q)(0) = id`, and `ex_q` an
  embedding on `O_q`.
* `LocalAddition.IsAffineIn L ψ`: `ψ(ex(p, V)) = ψ(p) + Tψ(p) V` for `p ∈ R₂ = ψ⁻¹(B₂(0))` and
  `|Tψ(p) V| ≤ 2` (the length `|V|_p` of the memoir, the metric being `ψ*`Euclidean there).
* `GoodExpData W`: charts `ψ_w`, `w ∈ W`, as in Definition 3.6 (2) (bijective onto `ℝ²ⁿ`,
  `ψ_w(w) = 0`, smooth, with disjoint closed domains), and a local addition affine in each `ψ_w`.
* Witness: `modelLocalAddition E` (`ex(q, v) = q + v` on `E`) and `modelGoodExpData`.
* `LocalAddition.IsGeodesicFor L g`: the curves `t ↦ ex(q, t v)`, `t ∈ [0,1]`, are locally
  minimizing with constant speed `|v|_g` for the Riemannian distance of `g` (Mathlib's
  `riemannianEDist`), i.e. `ex` is the exponential map of `g` on `O`.
* **`GeodesicExpInstance`** (named proposition): for a metric `g` that is the pull-back of the
  Euclidean metric over each `R₄(w)`, there is a local addition that is the geodesic exponential
  map of `g` and is affine in every `ψ_w`.  So the memoir's exponential map is one instance of the
  reading; the reading allows more maps.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff ENNReal
open Set Function Bundle Topology

noncomputable section

namespace GWMemoir

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

variable (E Q) in
/-- A **local addition** on `Q` (the reading of the exponential map of Definition 3.6 (3)): a
smooth map `ex` on an open, fibrewise convex neighbourhood `O` of the zero section of `TQ`, with
`ex(q, 0) = q`, `d(ex_q)(0) = id`, and `ex_q : O_q → Q` an embedding. -/
structure LocalAddition where
  O : Set (TangentBundle 𝓘(ℝ, E) Q)
  isOpen : IsOpen O
  zero_mem : ∀ q : Q, (⟨q, 0⟩ : TangentBundle 𝓘(ℝ, E) Q) ∈ O
  convex : ∀ q : Q,
    Convex ℝ {v : TangentSpace 𝓘(ℝ, E) q | (⟨q, v⟩ : TangentBundle 𝓘(ℝ, E) Q) ∈ O}
  ex : TangentBundle 𝓘(ℝ, E) Q → Q
  smooth : ContMDiffOn 𝓘(ℝ, E).tangent 𝓘(ℝ, E) ∞ ex O
  ex_zero : ∀ q : Q, ex ⟨q, 0⟩ = q
  deriv_zero : ∀ q : Q,
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun v : E => ex ⟨q, v⟩) 0 = ContinuousLinearMap.id ℝ E
  embedding : ∀ q : Q, IsEmbedding
    (fun v : {v : TangentSpace 𝓘(ℝ, E) q // (⟨q, v⟩ : TangentBundle 𝓘(ℝ, E) Q) ∈ O} =>
      ex ⟨q, v.1⟩)

namespace LocalAddition

variable (L : LocalAddition E Q)

/-- `exp_q(0) = q`. -/
theorem exp_zero (q : Q) : L.ex ⟨q, 0⟩ = q := L.ex_zero q

/-- `d exp_q(0) = id`. -/
theorem mfderiv_exp_zero (q : Q) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun v : E => L.ex ⟨q, v⟩) 0 = ContinuousLinearMap.id ℝ E :=
  L.deriv_zero q

/-- `exp` is smooth on `O`. -/
theorem contMDiffOn_exp : ContMDiffOn 𝓘(ℝ, E).tangent 𝓘(ℝ, E) ∞ L.ex L.O := L.smooth

/-- The segment `t ↦ (q, t v)`, `t ∈ [0,1]`, stays in `O` when `(q, v) ∈ O`. -/
theorem smul_mem {q : Q} {v : TangentSpace 𝓘(ℝ, E) q}
    (hv : (⟨q, v⟩ : TangentBundle 𝓘(ℝ, E) Q) ∈ L.O) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (⟨q, t • v⟩ : TangentBundle 𝓘(ℝ, E) Q) ∈ L.O := by
  have h := L.convex q (L.zero_mem q) hv (sub_nonneg.2 ht.2) ht.1 (by ring)
  simpa using h

/-- `ex` is **affine in the chart** `ψ` (Memoir p. 52): `ψ(ex(p, V)) = ψ(p) + Tψ(p) V` for
`p ∈ R₂ = ψ⁻¹(B₂(0))` and `|Tψ(p) V| ≤ 2`. -/
def IsAffineIn (ψ : OpenPartialHomeomorph Q E) : Prop :=
  ∀ p ∈ ψ.source, ‖ψ p‖ < 2 → ∀ V : TangentSpace 𝓘(ℝ, E) p,
    ‖(mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ p V : E)‖ ≤ 2 →
      L.ex ⟨p, V⟩ ∈ ψ.source ∧
        ψ (L.ex ⟨p, V⟩) = ψ p + (show E from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ p V)

end LocalAddition

variable (E Q) in
/-- The charts and the exponential map of Definition 3.6 (2)–(3), with the exponential map read as
a local addition: for `w ∈ W`, a smooth chart `ψ_w : (R(w), w) → (ℝ²ⁿ, 0)` onto `ℝ²ⁿ`, the closures
of the domains disjoint, and a local addition affine in every `ψ_w`. -/
structure GoodExpData (W : Finset Q) where
  ψ : Q → OpenPartialHomeomorph Q E
  mem_atlas : ∀ w ∈ W, ψ w ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ Q
  center : ∀ w ∈ W, w ∈ (ψ w).source ∧ ψ w w = 0
  onto : ∀ w ∈ W, (ψ w).target = univ
  disjoint : ∀ w ∈ W, ∀ w' ∈ W, w ≠ w' →
    Disjoint (closure (ψ w).source) (closure (ψ w').source)
  L : LocalAddition E Q
  affine : ∀ w ∈ W, L.IsAffineIn (ψ w)

/-! ## Witness: the model space -/

section Model

variable (E)

/-- The local addition `ex(q, v) = q + v` on the model space `E`, with `O = TE`. -/
def modelLocalAddition : LocalAddition E E where
  O := univ
  isOpen := isOpen_univ
  zero_mem _ := mem_univ _
  convex _ := by simpa using convex_univ
  ex p := p.proj + (show E from p.2)
  smooth := by
    have h' : ContMDiff 𝓘(ℝ, E × E) 𝓘(ℝ, E) ∞ (fun p : E × E => p.1 + p.2) :=
      contMDiff_iff_contDiff.2 (contDiff_fst.add contDiff_snd)
    have h : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (fun p : ModelProd E E => p.1 + p.2) := by
      rw [modelWithCornersSelf_prod] at h'; exact h'
    exact (h.comp (contMDiff_tangentBundleModelSpaceHomeomorph (I := 𝓘(ℝ, E)))).contMDiffOn
  ex_zero q := add_zero q
  deriv_zero q := by
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun v : E => q + v) 0 = _
    rw [mfderiv_eq_fderiv, fderiv_const_add]; exact fderiv_fun_id
  embedding q := (Homeomorph.addLeft q).isEmbedding.comp IsEmbedding.subtypeVal

/-- The chart `ψ = id` of the model space is in the maximal atlas, centred at `0`, onto `E`, and
`ex(q, v) = q + v` is affine in it. -/
theorem modelLocalAddition_isAffineIn :
    (modelLocalAddition E).IsAffineIn (chartAt E (0 : E)) := by
  intro p _ _ V _
  rw [chartAt_self_eq]
  refine ⟨mem_univ _, ?_⟩
  change p + (show E from V) = p + (show E from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) id p V)
  rw [mfderiv_id]; rfl

/-- **Witness**: the data of Definition 3.6 (2)–(3) in the local-addition reading exist on the
model space, with `W = {0}`. -/
def modelGoodExpData : GoodExpData E E {0} where
  ψ _ := chartAt E (0 : E)
  mem_atlas _ _ := IsManifold.chart_mem_maximalAtlas _
  center w hw := by
    rw [Finset.mem_singleton] at hw
    subst hw
    rw [chartAt_self_eq]; exact ⟨mem_univ _, rfl⟩
  onto _ _ := by rw [chartAt_self_eq]; rfl
  disjoint w hw w' hw' hne := by
    rw [Finset.mem_singleton] at hw hw'
    exact absurd (hw.trans hw'.symm) hne
  L := modelLocalAddition E
  affine _ _ := modelLocalAddition_isAffineIn E

end Model

/-! ## The geodesic exponential map as an instance -/

section Geodesic

/-- A smooth Riemannian metric on `Q`. -/
abbrev RiemMetric (E Q : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q] :=
  ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : Q => TangentSpace 𝓘(ℝ, E) x)

/-- The Riemannian distance of `g` (Mathlib's `riemannianEDist`, the infimum of the lengths of
`C¹` paths). -/
def riemDist (g : RiemMetric E Q) (x y : Q) : ℝ≥0∞ :=
  letI : RiemannianBundle (fun x : Q => TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
  Manifold.riemannianEDist 𝓘(ℝ, E) x y

/-- `g` is the pull-back of the Euclidean metric by `ψ` over `R_r = ψ⁻¹(B_r(0))`. -/
def IsFlatOver (g : RiemMetric E Q) (ψ : OpenPartialHomeomorph Q E) (r : ℝ) : Prop :=
  ∀ p ∈ ψ.source, ‖ψ p‖ < r → ∀ v w : TangentSpace 𝓘(ℝ, E) p,
    g.inner p v w = inner ℝ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ p v : E) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ p w)

/-- `ex` is the exponential map of `g` on `O`: for `(q, v) ∈ O` the curve `t ↦ ex(q, t v)`,
`t ∈ [0,1]`, is locally minimizing with constant speed `|v|_g` (a geodesic). -/
def LocalAddition.IsGeodesicFor (L : LocalAddition E Q) (g : RiemMetric E Q) : Prop :=
  ∀ (q : Q) (v : TangentSpace 𝓘(ℝ, E) q), (⟨q, v⟩ : TangentBundle 𝓘(ℝ, E) Q) ∈ L.O →
    ∀ t ∈ Icc (0 : ℝ) 1, ∃ ε > 0, ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1,
      |s - t| < ε → |s' - t| < ε →
        riemDist g (L.ex ⟨q, s • v⟩) (L.ex ⟨q, s' • v⟩) =
          ENNReal.ofReal (|s - s'| * √(g.inner q v v))

/-- **The memoir's exponential map is an instance of the reading** (named proposition): for a
smooth metric `g` that is the pull-back of the Euclidean metric by `ψ_w` over `R₄(w)` for every
`w ∈ W`, there is a local addition which is the geodesic exponential map of `g` on its domain and
is affine in every `ψ_w`.  (Classical: geodesics exist and are unique; the injectivity radius is
positive and continuous; in `R₄(w)` the geodesics are the straight lines of `ψ_w`.) -/
def GeodesicExpInstance (W : Finset Q) (ψ : Q → OpenPartialHomeomorph Q E) : Prop :=
  ∀ g : RiemMetric E Q, (∀ w ∈ W, IsFlatOver g (ψ w) 4) →
    ∃ L : LocalAddition E Q, L.IsGeodesicFor g ∧ ∀ w ∈ W, L.IsAffineIn (ψ w)

end Geodesic

end GWMemoir
