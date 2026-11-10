import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Convex.Measure
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.GroupTheory.Perm.Fin

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021): the Euclidean layer of
the integration of differential forms used in **Theorem 4.4.7** (p. 199; preprint Theorem 4.28,
Stokes' theorem, gap G.40), **Theorem 6.7.1** and the branched Stokes theorems of **§9.5**, with
the boundary orientation of **Definition 9.3.8** (p. 427).  Numbers and pages are the 2021 text's.

# Top-degree forms on `ℝⁿ`: integral, pull-back, change of variables, quadrants and faces

The text integrates classical forms over oriented finite-dimensional manifolds with boundary with
corners and uses Stokes' theorem; it gives no construction (Mathlib has `extDeriv` but no
integration of forms).  This file supplies the chart-level notions on
`ℝⁿ = EuclideanSpace ℝ (Fin n)` (the model space of Mathlib's `modelWithCornersEuclideanQuadrant`,
which the project's solution sets use, `Chapter9/MathlibSolutionSets.lean`).  A `k`-form on a
normed space `E` is Mathlib's `E → E [⋀^Fin k]→L[ℝ] ℝ`.

## What is formalized

* `stdFrame n`: the standard frame `(e₀, …, eₙ₋₁)` of `ℝⁿ`; `topFormIntegral s ω`: the integral
  `∫_s ω := ∫_{x ∈ s} ω(x)(e₀, …, eₙ₋₁) dx` of a top-degree form over a set, for the standard
  orientation.
* `formPullback φ φ' ω`: the pull-back `φ^*ω (x) = ω(φ x)(φ' x ·, …, φ' x ·)` by a map with a given
  derivative field `φ'` (Mathlib's `extDeriv_pullback` uses the same shape with `φ' = fderiv φ`),
  with the chain rule `formPullback_formPullback`.
* The key identity `alternatingMap_comp_eq_det_mul`: `f(A v₀, …, A vₙ₋₁) = det A · f(v)` for a
  top-degree form `f` and a linear map `A`.
* **Change of variables** (`topFormIntegral_image`, `_of_det_pos`, `_of_det_neg`): for `φ`
  injective on a measurable `s` with derivative `φ'` within `s`,
  `∫_{φ(s)} ω = ∫_s sign(det φ') · φ^*ω`; so `∫_{φ(s)} ω = ∫_s φ^*ω` if `det φ' > 0` on `s`
  (orientation-preserving charts) and `= -∫_s φ^*ω` if `det φ' < 0`.  This is Mathlib's
  `integral_image_eq_integral_abs_det_fderiv_smul` with the key identity.
* Quadrants `closedQuadrant S = {x | 0 ≤ xᵢ for i ∈ S}` (`S : Set (Fin m)`; `S = univ` is the
  range of `modelWithCornersEuclideanQuadrant m`, `range_modelWithCornersEuclideanQuadrant`;
  `S = {i | i < k}` is the model `[0,∞)ᵏ × ℝⁿ⁻ᵏ`): closed, convex, `UniqueDiffOn`, interior
  `openQuadrant S`, and the boundary (the union of the faces, with all corners) is a null set
  (`openQuadrant_ae_eq_quadrant`).
* The faces `{xᵢ = 0}` of `closedQuadrant S` (`i ∈ S`): the linear embedding
  `faceEmbedding i : ℝⁿ → ℝⁿ⁺¹`, `y ↦ (y₀, …, yᵢ₋₁, 0, yᵢ, …)`, which maps
  `closedQuadrant (i.succAbove ⁻¹' S)` onto the face (`image_faceEmbedding_quadrant`), the pull-back
  `facePullback i ω` of an `n`-form on `ℝⁿ⁺¹`, and the boundary-orientation sign
  `faceSign i = (-1)^(i+1)`.

## The boundary orientation

The text (Definition 9.3.8) orients `T_y∂M` at a point with `d_M(y) = 1` by the bases
`(a₁, …, aₙ₋₁)` for which `(e, a₁, …, aₙ₋₁)` is positive, `e` outward pointing ("outward normal
first").  At the face `{xᵢ = 0}` of `closedQuadrant S` the vector `-eᵢ` points outward
(`neg_stdFrame_not_mem_quadrant`), and the frame `faceEmbedding i ∘ stdFrame n =
(e_j)_{j ≠ i}` of the face satisfies
`det(-eᵢ, (e_j)_{j ≠ i}) = (-1)^(i+1) = faceSign i` (`det_cons_neg_stdFrame_faceFrame`).  So the
boundary orientation of the face is `faceSign i` times the orientation of its parametrization by
`faceEmbedding i`, and the face integral with the boundary orientation is
`faceSign i * topFormIntegral (closedQuadrant (i.succAbove ⁻¹' S)) (facePullback i ω)`; this is the
form in which `EuclideanStokes2021.lean` states Stokes' theorem.
-/

open Set MeasureTheory Filter Topology Module

noncomputable section

namespace Polyfold

/-! ### The standard frame and the integral of a top-degree form -/

section TopForm

variable {n : ℕ}

/-- The standard frame `(e₀, …, eₙ₋₁)` of `ℝⁿ = EuclideanSpace ℝ (Fin n)`. -/
def stdFrame (n : ℕ) : Fin n → EuclideanSpace ℝ (Fin n) :=
  ⇑(EuclideanSpace.basisFun (Fin n) ℝ)

theorem stdFrame_apply (i : Fin n) : stdFrame n i = EuclideanSpace.single i 1 :=
  EuclideanSpace.basisFun_apply _ _ i

theorem stdFrame_eq_toLp_single (i : Fin n) :
    stdFrame n i = WithLp.toLp 2 (Pi.single i (1 : ℝ)) := by
  rw [stdFrame_apply]; rfl

/-- The standard frame is the standard basis. -/
theorem coe_basisFun_toBasis : ⇑(EuclideanSpace.basisFun (Fin n) ℝ).toBasis = stdFrame n := by
  simp [stdFrame]

/-- **The integral of a top-degree form** over a set `s ⊆ ℝⁿ`, for the standard orientation:
`∫_s ω = ∫_{x ∈ s} ω(x)(e₀, …, eₙ₋₁) dx`. -/
def topFormIntegral (s : Set (EuclideanSpace ℝ (Fin n)))
    (ω : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) [⋀^Fin n]→L[ℝ] ℝ) : ℝ :=
  ∫ x in s, ω x (stdFrame n)

theorem topFormIntegral_def (s : Set (EuclideanSpace ℝ (Fin n)))
    (ω : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) [⋀^Fin n]→L[ℝ] ℝ) :
    topFormIntegral s ω = ∫ x in s, ω x (stdFrame n) := rfl

/-- Two forms that agree on a measurable set have the same integral over it. -/
theorem topFormIntegral_congr {s : Set (EuclideanSpace ℝ (Fin n))} (hs : MeasurableSet s)
    {ω₁ ω₂ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) [⋀^Fin n]→L[ℝ] ℝ}
    (h : EqOn ω₁ ω₂ s) : topFormIntegral s ω₁ = topFormIntegral s ω₂ :=
  setIntegral_congr_fun hs fun x hx => by rw [h hx]

/-- A form vanishing on `t \ s`, `s ⊆ t`, has the same integral over `s` and `t`. -/
theorem topFormIntegral_eq_of_subset {s t : Set (EuclideanSpace ℝ (Fin n))}
    (ht : MeasurableSet t) (hst : s ⊆ t)
    {ω : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) [⋀^Fin n]→L[ℝ] ℝ}
    (h : ∀ x ∈ t \ s, ω x = 0) : topFormIntegral t ω = topFormIntegral s ω :=
  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero ht hst fun x hx => by simp [h x hx]

/-- The integral is additive in the form (for integrable forms). -/
theorem topFormIntegral_finsetSum {ι : Type*} (u : Finset ι) {s : Set (EuclideanSpace ℝ (Fin n))}
    (ω : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ∀ j ∈ u, IntegrableOn (fun x => ω j x (stdFrame n)) s) :
    topFormIntegral s (fun x => ∑ j ∈ u, ω j x) = ∑ j ∈ u, topFormIntegral s (ω j) := by
  simp only [topFormIntegral, ContinuousAlternatingMap.sum_apply]
  exact integral_finsetSum u hω

end TopForm

/-! ### The key identity: a top-degree form scales by the determinant -/

section Det

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} [Finite ι]

/-- **The key identity.** For a top-degree alternating form `f` on `E` (a basis of `E` is indexed
by `ι`) and a linear map `A`, `f(A v) = det A · f(v)`. -/
theorem alternatingMap_comp_eq_det_mul (b : Basis ι ℝ E) (f : E [⋀^ι]→L[ℝ] ℝ) (A : E →L[ℝ] E)
    (v : ι → E) : f (A ∘ v) = A.det * f v := by
  classical
  cases nonempty_fintype ι
  have key : ∀ w, f w = f b * b.det w := fun w => by
    have := congrArg (fun g => g w) (AlternatingMap.eq_smul_basis_det b f.toAlternatingMap)
    simpa using this
  rw [key, key v]
  have : b.det (A ∘ v) = LinearMap.det (A : E →ₗ[ℝ] E) * b.det v := b.det_comp (A : E →ₗ[ℝ] E) v
  rw [this, ContinuousLinearMap.det]
  ring

end Det

/-! ### Pull-back and change of variables -/

section Pullback

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] {ι : Type*}

/-- **The pull-back** `φ^*ω` of a form `ω` on `F` by a map `φ : E → F` with derivative field `φ'`:
`(φ^*ω)(x)(v) = ω(φ x)(φ' x ∘ v)`.  With `φ' = fderiv ℝ φ` this is the pull-back of Mathlib's
`extDeriv_pullback`; with `φ' = fderivWithin ℝ φ s` the one of `extDerivWithin_pullback`. -/
def formPullback (φ : E → F) (φ' : E → E →L[ℝ] F) (ω : F → F [⋀^ι]→L[ℝ] G) (x : E) :
    E [⋀^ι]→L[ℝ] G :=
  (ω (φ x)).compContinuousLinearMap (φ' x)

@[simp]
theorem formPullback_apply (φ : E → F) (φ' : E → E →L[ℝ] F) (ω : F → F [⋀^ι]→L[ℝ] G) (x : E)
    (v : ι → E) : formPullback φ φ' ω x v = ω (φ x) (φ' x ∘ v) := rfl

/-- **The chain rule for pull-backs**: `ψ^*(φ^*ω) = (φ ∘ ψ)^*ω` with the derivative field
`φ'(ψ x) ∘ ψ'(x)`. -/
theorem formPullback_formPullback {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (ψ : D → E) (ψ' : D → D →L[ℝ] E) (φ : E → F) (φ' : E → E →L[ℝ] F)
    (ω : F → F [⋀^ι]→L[ℝ] G) :
    formPullback ψ ψ' (formPullback φ φ' ω) =
      formPullback (φ ∘ ψ) (fun x => (φ' (ψ x)).comp (ψ' x)) ω := by
  funext x
  ext v
  rfl

/-- The pull-back by the identity is the identity. -/
@[simp]
theorem formPullback_id (ω : E → E [⋀^ι]→L[ℝ] G) :
    formPullback id (fun _ => ContinuousLinearMap.id ℝ E) ω = ω := by
  funext x
  ext v
  rfl

end Pullback

section ChangeOfVariables

variable {n : ℕ} {s : Set (EuclideanSpace ℝ (Fin n))}
  {φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
  {φ' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}

/-- `φ^*ω (e) = det φ' · ω(φ x)(e)` for a top-degree form. -/
theorem formPullback_stdFrame
    (ω : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) [⋀^Fin n]→L[ℝ] ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    formPullback φ φ' ω x (stdFrame n) = (φ' x).det * ω (φ x) (stdFrame n) := by
  rw [formPullback_apply,
    alternatingMap_comp_eq_det_mul (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]

/-- **Change of variables for top-degree forms.** For `φ` injective on a measurable set `s` with
derivative `φ'` within `s`, `∫_{φ(s)} ω = ∫_s sign(det φ') · φ^*ω`. -/
theorem topFormIntegral_image (hs : MeasurableSet s)
    (hφ' : ∀ x ∈ s, HasFDerivWithinAt φ (φ' x) s x) (hφ : InjOn φ s)
    (ω : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) [⋀^Fin n]→L[ℝ] ℝ) :
    topFormIntegral (φ '' s) ω =
      ∫ x in s, (SignType.sign (φ' x).det : ℝ) * formPullback φ φ' ω x (stdFrame n) := by
  rw [topFormIntegral, integral_image_eq_integral_abs_det_fderiv_smul volume hs hφ' hφ]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [formPullback_stdFrame, smul_eq_mul, ← mul_assoc, sign_mul_self]

/-- **Change of variables, orientation-preserving case**: if `det φ' > 0` on `s`,
`∫_{φ(s)} ω = ∫_s φ^*ω`. -/
theorem topFormIntegral_image_of_det_pos (hs : MeasurableSet s)
    (hφ' : ∀ x ∈ s, HasFDerivWithinAt φ (φ' x) s x) (hφ : InjOn φ s)
    (hdet : ∀ x ∈ s, 0 < (φ' x).det)
    (ω : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) [⋀^Fin n]→L[ℝ] ℝ) :
    topFormIntegral (φ '' s) ω = topFormIntegral s (formPullback φ φ' ω) := by
  rw [topFormIntegral_image hs hφ' hφ, topFormIntegral]
  refine setIntegral_congr_fun hs fun x hx => ?_
  simp [sign_pos (hdet x hx)]

/-- **Change of variables, orientation-reversing case**: if `det φ' < 0` on `s`,
`∫_{φ(s)} ω = -∫_s φ^*ω`. -/
theorem topFormIntegral_image_of_det_neg (hs : MeasurableSet s)
    (hφ' : ∀ x ∈ s, HasFDerivWithinAt φ (φ' x) s x) (hφ : InjOn φ s)
    (hdet : ∀ x ∈ s, (φ' x).det < 0)
    (ω : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) [⋀^Fin n]→L[ℝ] ℝ) :
    topFormIntegral (φ '' s) ω = -topFormIntegral s (formPullback φ φ' ω) := by
  rw [topFormIntegral_image hs hφ' hφ, topFormIntegral, ← integral_neg]
  refine setIntegral_congr_fun hs fun x hx => ?_
  simp [sign_neg (hdet x hx)]

end ChangeOfVariables

/-! ### Quadrants -/

section Quadrant

variable {m : ℕ} {S : Set (Fin m)} {x : EuclideanSpace ℝ (Fin m)}

/-- The quadrant `{x | 0 ≤ xᵢ for i ∈ S}` of `ℝᵐ`.  For `S = univ` it is the range of Mathlib's
model `modelWithCornersEuclideanQuadrant m`; for `S = {i | i < k}` it is `[0,∞)ᵏ × ℝᵐ⁻ᵏ`. -/
def closedQuadrant (S : Set (Fin m)) : Set (EuclideanSpace ℝ (Fin m)) := {x | ∀ i ∈ S, 0 ≤ x i}

/-- The open quadrant `{x | 0 < xᵢ for i ∈ S}`, the interior of `closedQuadrant S`. -/
def openQuadrant (S : Set (Fin m)) : Set (EuclideanSpace ℝ (Fin m)) := {x | ∀ i ∈ S, 0 < x i}

theorem mem_quadrant : x ∈ closedQuadrant S ↔ ∀ i ∈ S, 0 ≤ x i := Iff.rfl

theorem mem_openQuadrant : x ∈ openQuadrant S ↔ ∀ i ∈ S, 0 < x i := Iff.rfl

theorem range_modelWithCornersEuclideanQuadrant :
    range (modelWithCornersEuclideanQuadrant m) = closedQuadrant univ := by
  rw [show ⇑(modelWithCornersEuclideanQuadrant m) = Subtype.val from rfl,
    range_euclideanQuadrant]
  ext x; simp [closedQuadrant]

@[simp]
theorem quadrant_empty : closedQuadrant (∅ : Set (Fin m)) = univ := by ext; simp [closedQuadrant]

theorem quadrant_eq_biInter :
    closedQuadrant S = ⋂ i ∈ S, {x : EuclideanSpace ℝ (Fin m) | 0 ≤ x i} := by
  ext; simp [closedQuadrant]

theorem openQuadrant_eq_biInter :
    openQuadrant S = ⋂ i ∈ S, {x : EuclideanSpace ℝ (Fin m) | 0 < x i} := by
  ext; simp [openQuadrant]

theorem isClosed_quadrant : IsClosed (closedQuadrant S) := by
  rw [quadrant_eq_biInter]
  exact isClosed_biInter fun i _ => isClosed_le continuous_const (PiLp.continuous_apply 2 _ i)

theorem measurableSet_quadrant : MeasurableSet (closedQuadrant S) := isClosed_quadrant.measurableSet

theorem isOpen_openQuadrant : IsOpen (openQuadrant S) := by
  rw [openQuadrant_eq_biInter]
  exact S.toFinite.isOpen_biInter fun i _ =>
    isOpen_lt continuous_const (PiLp.continuous_apply 2 _ i)

theorem openQuadrant_subset_quadrant : openQuadrant S ⊆ closedQuadrant S :=
  fun _ hx i hi => (hx i hi).le

theorem interior_closedQuadrant : interior (closedQuadrant S) = openQuadrant S := by
  rw [quadrant_eq_biInter, openQuadrant_eq_biInter, S.toFinite.interior_biInter]
  exact iInter₂_congr fun i _ => interior_halfSpace 2 0 i

theorem convex_quadrant : Convex ℝ (closedQuadrant S) := fun x hx y hy a b ha hb _ i hi => by
  have := hx i hi
  have := hy i hi
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  positivity

theorem uniqueDiffOn_quadrant : UniqueDiffOn ℝ (closedQuadrant S) :=
  uniqueDiffOn_convex convex_quadrant
    ⟨WithLp.toLp 2 fun _ => 1, by simp [interior_closedQuadrant, openQuadrant]⟩

/-- The quadrant is a neighbourhood of the points of the open quadrant. -/
theorem quadrant_mem_nhds (hx : x ∈ openQuadrant S) : closedQuadrant S ∈ 𝓝 x :=
  mem_of_superset (isOpen_openQuadrant.mem_nhds hx) openQuadrant_subset_quadrant

/-- **The boundary of a quadrant is a null set**: the union of its faces, with all the corners,
has measure zero (`Convex.addHaar_frontier`). -/
theorem openQuadrant_ae_eq_quadrant :
    openQuadrant S =ᵐ[volume] (closedQuadrant S : Set (EuclideanSpace ℝ (Fin m))) := by
  rw [← interior_closedQuadrant]
  exact interior_ae_eq_of_null_frontier (convex_quadrant.addHaar_frontier volume)

/-- Integrals over a quadrant and over the open quadrant agree. -/
theorem setIntegral_openQuadrant {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : EuclideanSpace ℝ (Fin m) → F) :
    ∫ x in openQuadrant S, f x = ∫ x in closedQuadrant S, f x :=
  setIntegral_congr_set openQuadrant_ae_eq_quadrant

end Quadrant

/-! ### The faces of a quadrant and the boundary orientation -/

section Face

variable {n : ℕ}

/-- The linear map `y ↦ (y₀, …, yᵢ₋₁, 0, yᵢ, …, yₙ₋₁)`, `ℝⁿ → ℝⁿ⁺¹`. -/
def faceEmbeddingₗ (i : Fin (n + 1)) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) where
  toFun y := WithLp.toLp 2 (i.insertNth (α := fun _ => ℝ) 0 (WithLp.ofLp y))
  map_add' y z := by
    ext j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩ <;> simp
  map_smul' c y := by
    ext j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩ <;> simp

/-- **The parametrization of the face `{xᵢ = 0}`**: the linear embedding
`y ↦ (y₀, …, yᵢ₋₁, 0, yᵢ, …, yₙ₋₁)`, `ℝⁿ → ℝⁿ⁺¹`. -/
def faceEmbedding (i : Fin (n + 1)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  LinearMap.toContinuousLinearMap (faceEmbeddingₗ i)

theorem faceEmbedding_apply (i : Fin (n + 1)) (y : EuclideanSpace ℝ (Fin n)) :
    faceEmbedding i y = WithLp.toLp 2 (i.insertNth (α := fun _ => ℝ) 0 (WithLp.ofLp y)) := rfl

@[simp]
theorem faceEmbedding_apply_self (i : Fin (n + 1)) (y : EuclideanSpace ℝ (Fin n)) :
    faceEmbedding i y i = 0 := by
  simp [faceEmbedding_apply]

@[simp]
theorem faceEmbedding_apply_succAbove (i : Fin (n + 1)) (y : EuclideanSpace ℝ (Fin n))
    (j : Fin n) : faceEmbedding i y (i.succAbove j) = y j := by
  simp [faceEmbedding_apply]

/-- The face embedding maps the standard frame of `ℝⁿ` to the frame `(e_j)_{j ≠ i}` of the face. -/
theorem faceEmbedding_comp_stdFrame (i : Fin (n + 1)) :
    faceEmbedding i ∘ stdFrame n = i.removeNth (stdFrame (n + 1)) := by
  funext j
  ext k
  simp only [Function.comp_apply, Fin.removeNth, stdFrame_eq_toLp_single]
  rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨l, rfl⟩
  · simp [faceEmbedding_apply, (Fin.succAbove_ne k j).symm]
  · simp [faceEmbedding_apply, Pi.single_apply]

/-- The projection `x ↦ (x_j)_{j ≠ i}` inverts the face embedding on the hyperplane `{xᵢ = 0}`. -/
theorem faceEmbedding_removeNth {i : Fin (n + 1)} {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : x i = 0) : faceEmbedding i (WithLp.toLp 2 (i.removeNth (WithLp.ofLp x))) = x := by
  ext k
  rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨l, rfl⟩
  · simp [hx]
  · simp [Fin.removeNth]

theorem preimage_faceEmbedding_quadrant (S : Set (Fin (n + 1))) (i : Fin (n + 1)) :
    faceEmbedding i ⁻¹' closedQuadrant S = closedQuadrant (i.succAbove ⁻¹' S) := by
  ext y
  simp only [mem_preimage, mem_quadrant]
  rw [Fin.forall_iff_succAbove i]
  simp

/-- The face embedding maps `closedQuadrant (i.succAbove ⁻¹' S)` onto the face
`{x ∈ closedQuadrant S | xᵢ = 0}`. -/
theorem image_faceEmbedding_quadrant (S : Set (Fin (n + 1))) (i : Fin (n + 1)) :
    faceEmbedding i '' closedQuadrant (i.succAbove ⁻¹' S) = closedQuadrant S ∩ {x | x i = 0} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← preimage_faceEmbedding_quadrant] at hy
    exact ⟨hy, faceEmbedding_apply_self i y⟩
  · rintro ⟨hxS, hx⟩
    refine ⟨_, ?_, faceEmbedding_removeNth hx⟩
    rw [← preimage_faceEmbedding_quadrant, mem_preimage, faceEmbedding_removeNth hx]
    exact hxS

/-- **The points of the face with `d = 1`.**  For `i ∈ S`, the face embedding maps the open
quadrant `openQuadrant (i.succAbove ⁻¹' S)` onto the points `x` of `closedQuadrant S` at which
`xᵢ` is the only vanishing coordinate in `S`, i.e. the points of the face `{xᵢ = 0}` of degeneracy
index `d(x) = 1` (Definition 9.3.8 orients `∂M` at these points).  The rest of the face, the corners
of codimension `≥ 2`, is the null set `closedQuadrant \ openQuadrant` of the face
(`openQuadrant_ae_eq_quadrant`), so it does not contribute to the face integral. -/
theorem image_faceEmbedding_openQuadrant {S : Set (Fin (n + 1))} {i : Fin (n + 1)} (hi : i ∈ S) :
    faceEmbedding i '' openQuadrant (i.succAbove ⁻¹' S) =
      {x | x ∈ closedQuadrant S ∧ ∀ j ∈ S, x j = 0 ↔ j = i} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, fun j hj => ?_⟩
    · rw [← mem_preimage, preimage_faceEmbedding_quadrant]
      exact openQuadrant_subset_quadrant hy
    · rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨l, rfl⟩
      · simp
      · simp only [faceEmbedding_apply_succAbove, Fin.succAbove_ne, iff_false]
        exact (hy l hj).ne'
  · rintro ⟨hxS, hx⟩
    have hxi : x i = 0 := (hx i hi).2 rfl
    refine ⟨_, fun l hl => ?_, faceEmbedding_removeNth hxi⟩
    have h0 : x (i.succAbove l) ≠ 0 := fun h => Fin.succAbove_ne i l ((hx _ hl).1 h)
    exact (hxS _ hl).lt_of_ne' (by simpa [Fin.removeNth] using h0)

/-- The pull-back `ιᵢ^*ω` of an `n`-form on `ℝⁿ⁺¹` to the face parameter space `ℝⁿ` by the face
embedding `ιᵢ = faceEmbedding i` (a linear map, its own derivative). -/
def facePullback (i : Fin (n + 1))
    (ω : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) [⋀^Fin n]→L[ℝ] ℝ) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) [⋀^Fin n]→L[ℝ] ℝ :=
  formPullback (faceEmbedding i) (fun _ => faceEmbedding i) ω

theorem facePullback_stdFrame (i : Fin (n + 1))
    (ω : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) [⋀^Fin n]→L[ℝ] ℝ)
    (y : EuclideanSpace ℝ (Fin n)) :
    facePullback i ω y (stdFrame n) = ω (faceEmbedding i y) (i.removeNth (stdFrame (n + 1))) := by
  rw [facePullback, formPullback_apply, faceEmbedding_comp_stdFrame]

/-- The sign `(-1)^(i+1)` of the boundary orientation of the face `{xᵢ = 0}` relative to its
parametrization by `faceEmbedding i` (`det_cons_neg_stdFrame_faceFrame`). -/
def faceSign (i : Fin (n + 1)) : ℝ := (-1) ^ ((i : ℕ) + 1)

/-- `-eᵢ` points out of the quadrant at the face `{xᵢ = 0}`, `i ∈ S`. -/
theorem add_smul_neg_stdFrame_not_mem_quadrant {S : Set (Fin (n + 1))} {i : Fin (n + 1)}
    (hi : i ∈ S) {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x i = 0) {t : ℝ} (ht : 0 < t) :
    x + t • (-stdFrame (n + 1) i) ∉ closedQuadrant S := fun h => by
  have := h i hi
  simp [stdFrame_apply, hx] at this
  linarith

/-- **The boundary orientation, outward normal first** (Definition 9.3.8): with the outward vector
`-eᵢ` at the face `{xᵢ = 0}`, `det(-eᵢ, (e_j)_{j ≠ i}) = (-1)^(i+1) = faceSign i`, where
`(e_j)_{j ≠ i} = faceEmbedding i ∘ stdFrame n` is the frame of the face parametrization.  So the
frame `faceEmbedding i ∘ stdFrame n` is positive for the boundary orientation iff
`faceSign i = 1`. -/
theorem det_cons_neg_stdFrame_faceFrame (i : Fin (n + 1)) :
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.det
        (Fin.cons (-stdFrame (n + 1) i) (faceEmbedding i ∘ stdFrame n)) = faceSign i := by
  set b := (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis
  rw [faceEmbedding_comp_stdFrame, ← neg_one_smul ℝ (stdFrame (n + 1) i)]
  have h1 := b.det.toMultilinearMap.cons_smul (i.removeNth (stdFrame (n + 1))) (-1)
    (stdFrame (n + 1) i)
  simp only [AlternatingMap.coe_multilinearMap] at h1
  rw [h1, Fin.cons_removeNth_eq_comp_cycleRange_symm, AlternatingMap.map_perm,
    ← coe_basisFun_toBasis, b.det_self, Equiv.Perm.sign_symm, Fin.sign_cycleRange, faceSign]
  simp [Units.smul_def, pow_succ]

end Face

end Polyfold
