import Polyfold.Chapter6.FredholmDet
import Polyfold.Chapter1.FredholmIndex
import Polyfold.Chapter1.FredholmPerturbation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.3,
pp. 207–208: **Definition 6.4.3 (preprint 6.9)** (good left-projections `Π_T` and their order) and **Lemma 6.10**
(two good left-projections have a common lower bound) *(book 2017: Definition 6.5; Lemma 6.10 is
not in the 2017 version, see below and `BookConcordance.md`)*.

# Good left-projections

## The text, paraphrased

(Definition 6.4.3 (preprint 6.9)) Let `T : E → F` be Fredholm.  A good left-projection for `T` is a bounded
projection `P : F → F` with (1) `dim(F / R(P)) < ∞` and (2) `R(P ∘ T) = R(P)`; `Π_T` is the set
of them.  Then `P` is Fredholm of index `0`, `P ∘ T` is Fredholm and `ind(P ∘ T) = ind(T)`.  `Π_T`
is partially ordered by `P ≤ Q` iff `P = PQ = QP`.  For `P, P' ∈ Π_T`, `R(P) ∩ R(P')` has finite
codimension.  (Lemma 6.10) Given `P, P' ∈ Π_T` there is `P'' ∈ Π_T` with `P'' ≤ P` and
`P'' ≤ P'`.  The proof takes complements `X`, `X'` of `R(P) ∩ R(P')` in `R(P)`, `R(P')`, a
complement `Z` of `X ⊕ X' ⊕ R(P) ∩ R(P')`, and `P''` the projection onto `R(P) ∩ R(P')` along
`Z ⊕ X ⊕ X'`.

## What is formalized

* `Polyfold.IsGoodLeftProj T P` (**Definition 6.4.3 (preprint 6.9)**), `Polyfold.goodLeftProjs T` (`Π_T`),
  `Polyfold.ProjLE P Q` (`P = PQ = QP`) with `ProjLE.refl`, `ProjLE.antisymm`, `ProjLE.trans`
  (a partial order on projections).
* The remarks after the definition: `IsGoodLeftProj.isFredholm` and
  `IsGoodLeftProj.fredholmIndex_eq_zero` (`P` is Fredholm of index `0`),
  `IsGoodLeftProj.isFredholm_comp` and `IsGoodLeftProj.fredholmIndex_comp` (`P ∘ T` is Fredholm,
  `ind(P ∘ T) = ind(T)`), `IsGoodLeftProj.finiteDimensional_quotient_inf` (`R(P) ∩ R(P')` has
  finite codimension).
* `Polyfold.exists_isGoodLeftProj`: `Π_T` is not empty for `T` Fredholm (the projection onto
  `R(T)` along a finite-dimensional complement), which the text uses without stating it.
* **Lemma 6.10** (`lemma_6_10_preprint`), without the hypothesis that `T` is Fredholm, by a construction that
  differs from the text's (below).
* `lemma_6_10_text_reading_preprint`: on `F = ℝ²` with `T = 1` there are `P, P' ∈ Π_T` such that **no**
  projection with range `R(P) ∩ R(P')` lies below both; so the text's `P''` (whose range is
  `R(P) ∩ R(P')`) does not satisfy `P'' = P'' P` and `P'' = P'' P'` as we read it.

## Reading and the construction used

The claim `P'' = P'' P` in the text's proof needs `ker P ⊆ ker P''`, which fails for the text's
`P''` in general: with `P` the projection of `ℝ²` onto the `x`-axis along the `y`-axis and `P'`
the projection onto the `x`-axis along the diagonal, `R(P) ∩ R(P')` is the `x`-axis, and a
projection onto it below both `P` and `P'` would equal both.  The lemma itself holds: with
`K = ker P + ker P'` (finite-dimensional), a closed finite-codimensional `N` with `N ∩ K = 0`
(Hahn–Banach), `R'' = R(P) ∩ R(P') ∩ N` and a closed complement `C ⊇ K` of `R''`, the projection
`P''` onto `R''` along `C` satisfies `P'' = P P'' = P'' P` (since `x − P x ∈ ker P ⊆ C`) and the
same for `P'`, and `R(P'' T) = P''(R(P T)) = P''(R(P)) = R(P'')`.  The 2017 version drops the lemma
and remarks that such a common lower bound need not exist in general; with the conventions above it
exists (Findings, Chapter 6).
-/

open Module

noncomputable section

namespace Polyfold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Definition 6.4.3 (preprint 6.9)**: a **good left-projection** for `T : E → F` is a bounded projection
`P : F → F` with (1) `dim(F / R(P)) < ∞` and (2) `R(P ∘ T) = R(P)`. -/
structure IsGoodLeftProj (T : E →L[ℝ] F) (P : F →L[ℝ] F) : Prop where
  /-- `P` is a projection. -/
  isProj : P ∘L P = P
  /-- (1) `dim(F / R(P)) < ∞`. -/
  finite_coker : FiniteDimensional ℝ (F ⧸ LinearMap.range (P : F →ₗ[ℝ] F))
  /-- (2) `R(P ∘ T) = R(P)`. -/
  range_comp : LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) =
    LinearMap.range (P : F →ₗ[ℝ] F)

/-- `Π_T`, the set of good left-projections for `T`. -/
def goodLeftProjs (T : E →L[ℝ] F) : Set (F →L[ℝ] F) := {P | IsGoodLeftProj T P}

/-- The order on projections: `P ≤ Q` if and only if `P = PQ = QP`. -/
def ProjLE (P Q : F →L[ℝ] F) : Prop := P = P ∘L Q ∧ P = Q ∘L P

omit [CompleteSpace F] in
/-- `≤` is reflexive on projections. -/
theorem ProjLE.refl {P : F →L[ℝ] F} (hP : P ∘L P = P) : ProjLE P P := ⟨hP.symm, hP.symm⟩

omit [CompleteSpace F] in
/-- `≤` is antisymmetric. -/
theorem ProjLE.antisymm {P Q : F →L[ℝ] F} (h : ProjLE P Q) (h' : ProjLE Q P) : P = Q :=
  h.1.trans h'.2.symm

omit [CompleteSpace F] in
/-- `≤` is transitive. -/
theorem ProjLE.trans {P Q R : F →L[ℝ] F} (h : ProjLE P Q) (h' : ProjLE Q R) : ProjLE P R := by
  constructor
  · calc P = P ∘L Q := h.1
      _ = P ∘L (Q ∘L R) := by rw [← h'.1]
      _ = (P ∘L Q) ∘L R := (ContinuousLinearMap.comp_assoc _ _ _).symm
      _ = P ∘L R := by rw [← h.1]
  · calc P = Q ∘L P := h.2
      _ = (R ∘L Q) ∘L P := by rw [← h'.2]
      _ = R ∘L (Q ∘L P) := ContinuousLinearMap.comp_assoc _ _ _
      _ = R ∘L P := by rw [← h.2]

omit [CompleteSpace F] in
/-- A projection `P ∘ P = P` is the identity on its range. -/
theorem proj_apply_eq_self_of_mem_range {P : F →L[ℝ] F} (hP : P ∘L P = P) {y : F}
    (hy : y ∈ LinearMap.range (P : F →ₗ[ℝ] F)) : P y = y := by
  obtain ⟨z, rfl⟩ := hy
  exact DFunLike.congr_fun hP z

omit [CompleteSpace F] in
/-- The range and the kernel of a continuous projection are topological complements. -/
theorem isTopCompl_range_ker_of_comp_self {P : F →L[ℝ] F} (hP : P ∘L P = P) :
    Submodule.IsTopCompl (LinearMap.range (P : F →ₗ[ℝ] F)) (LinearMap.ker (P : F →ₗ[ℝ] F)) :=
  ContinuousLinearMap.IsIdempotentElem.isTopCompl hP

namespace IsGoodLeftProj

variable {T : E →L[ℝ] F} {P : F →L[ℝ] F}

omit [CompleteSpace E] [CompleteSpace F] in
/-- `ker P` is finite-dimensional: it is isomorphic to `F / R(P)`. -/
theorem finiteDimensional_ker (hP : IsGoodLeftProj T P) :
    FiniteDimensional ℝ (LinearMap.ker (P : F →ₗ[ℝ] F)) :=
  have := hP.finite_coker
  (Submodule.quotientEquivOfIsCompl _ _ (isTopCompl_range_ker_of_comp_self hP.isProj).isCompl
    ).finiteDimensional

omit [CompleteSpace E] [CompleteSpace F] in
/-- `R(P) = ker(1 − P)` is closed. -/
theorem isClosed_range (hP : IsGoodLeftProj T P) :
    IsClosed (LinearMap.range (P : F →ₗ[ℝ] F) : Set F) :=
  (isTopCompl_range_ker_of_comp_self hP.isProj).isClosed

omit [CompleteSpace E] in
/-- A good left-projection is Fredholm (`dim ker P = dim coker P < ∞`). -/
theorem isFredholm (hP : IsGoodLeftProj T P) : P.IsFredholm :=
  isFredholm_of_banach P hP.finiteDimensional_ker hP.isClosed_range hP.finite_coker

omit [CompleteSpace E] [CompleteSpace F] in
/-- A good left-projection has index `0`. -/
theorem fredholmIndex_eq_zero (hP : IsGoodLeftProj T P) : fredholmIndex P = 0 := by
  have := hP.finite_coker
  have := hP.finiteDimensional_ker
  unfold fredholmIndex linIndex
  rw [← (Submodule.quotientEquivOfIsCompl _ _
    (isTopCompl_range_ker_of_comp_self hP.isProj).isCompl).finrank_eq, sub_self]

/-- `P ∘ T` is Fredholm. -/
theorem isFredholm_comp (hT : T.IsFredholm) (hP : IsGoodLeftProj T P) : (P ∘L T).IsFredholm := by
  have h := (IsFredholm.hasFiniteIndex hT).comp (IsFredholm.hasFiniteIndex hP.isFredholm)
  refine isFredholm_of_banach _ h.finite_ker ?_ h.finite_coker
  rw [hP.range_comp]
  exact hP.isClosed_range

omit [CompleteSpace E] in
/-- `ind(P ∘ T) = ind(T)`. -/
theorem fredholmIndex_comp (hT : T.IsFredholm) (hP : IsGoodLeftProj T P) :
    fredholmIndex (P ∘L T) = fredholmIndex T := by
  have h := linIndex_comp (IsFredholm.hasFiniteIndex hT) (IsFredholm.hasFiniteIndex hP.isFredholm)
  have h0 := hP.fredholmIndex_eq_zero
  unfold fredholmIndex at h0 ⊢
  exact h.trans (by rw [h0, add_zero])

omit [CompleteSpace E] [CompleteSpace F] in
/-- For `P, P' ∈ Π_T`, `R(P) ∩ R(P')` has finite codimension. -/
theorem finiteDimensional_quotient_inf {P' : F →L[ℝ] F} (hP : IsGoodLeftProj T P)
    (hP' : IsGoodLeftProj T P') :
    FiniteDimensional ℝ
      (F ⧸ (LinearMap.range (P : F →ₗ[ℝ] F) ⊓ LinearMap.range (P' : F →ₗ[ℝ] F))) :=
  Submodule.CoFG.inf hP.finite_coker hP'.finite_coker

end IsGoodLeftProj

omit [CompleteSpace E] [CompleteSpace F] in
/-- `Π_T` is not empty for a Fredholm operator `T`. -/
theorem exists_isGoodLeftProj {T : E →L[ℝ] F} (hT : T.IsFredholm) : ∃ P, IsGoodLeftProj T P := by
  obtain ⟨q, hq⟩ := hT.closedComplemented_range.exists_isTopCompl
  have key : ∀ x, (LinearMap.range (T : E →ₗ[ℝ] F)).projectionL q hq (T x) = T x := fun x =>
    Submodule.projectionL_apply_left hq ⟨T x, LinearMap.mem_range_self _ x⟩
  refine ⟨(LinearMap.range (T : E →ₗ[ℝ] F)).projectionL q hq,
    Submodule.isIdempotentElem_projectionL hq, ?_, ?_⟩
  · rw [Submodule.range_projectionL]
    exact hT.finite_coker
  · rw [Submodule.range_projectionL]
    ext y
    simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_comp,
      Function.comp_apply, key]

omit [CompleteSpace F] in
/-- A criterion for `P'' ≤ Q`: if `P''` is the continuous projection onto `R''` along `C`, and `Q`
is a projection with `R'' ⊆ R(Q)` and `ker Q ⊆ C`, then `P'' = P'' Q = Q P''`. -/
theorem projLE_projectionL {R'' C : Submodule ℝ F} (h : Submodule.IsTopCompl R'' C)
    {Q : F →L[ℝ] F} (hQ : Q ∘L Q = Q) (hker : LinearMap.ker (Q : F →ₗ[ℝ] F) ≤ C)
    (hr : R'' ≤ LinearMap.range (Q : F →ₗ[ℝ] F)) : ProjLE (R''.projectionL C h) Q := by
  constructor
  · ext x
    have hQx : Q (Q x) = Q x := DFunLike.congr_fun hQ x
    have hx : x - Q x ∈ C := hker (by
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, hQx, sub_self])
    have := Submodule.projectionL_apply_eq_zero_of_mem_right h hx
    rw [map_sub, sub_eq_zero] at this
    exact this
  · ext x
    exact (proj_apply_eq_self_of_mem_range hQ (hr (Submodule.projectionL_apply_mem h x))).symm

omit [CompleteSpace E] [CompleteSpace F] in
/-- If `P'' = P'' P` and `R(P T) = R(P)`, then `R(P'' T) = R(P'')`. -/
theorem range_comp_eq_of_comp_eq {T : E →L[ℝ] F} {P P'' : F →L[ℝ] F} (hP : IsGoodLeftProj T P)
    (h : P'' ∘L P = P'') :
    LinearMap.range ((P'' ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) =
      LinearMap.range (P'' : F →ₗ[ℝ] F) := by
  calc LinearMap.range ((P'' ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)
      = LinearMap.range ((P'' ∘L (P ∘L T) : E →L[ℝ] F) : E →ₗ[ℝ] F) := by
        rw [← ContinuousLinearMap.comp_assoc, h]
    _ = Submodule.map (P'' : F →ₗ[ℝ] F) (LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)) :=
        LinearMap.range_comp _ _
    _ = Submodule.map (P'' : F →ₗ[ℝ] F) (LinearMap.range (P : F →ₗ[ℝ] F)) := by
        rw [hP.range_comp]
    _ = LinearMap.range ((P'' ∘L P : F →L[ℝ] F) : F →ₗ[ℝ] F) := (LinearMap.range_comp _ _).symm
    _ = LinearMap.range (P'' : F →ₗ[ℝ] F) := by rw [h]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Lemma 6.10**: given `P, P' ∈ Π_T`, there is `P'' ∈ Π_T` with `P'' ≤ P` and `P'' ≤ P'`. -/
theorem lemma_6_10_preprint {T : E →L[ℝ] F} {P P' : F →L[ℝ] F} (hP : IsGoodLeftProj T P)
    (hP' : IsGoodLeftProj T P') :
    ∃ P'' : F →L[ℝ] F, IsGoodLeftProj T P'' ∧ ProjLE P'' P ∧ ProjLE P'' P' := by
  -- `K = ker P + ker P'` is finite-dimensional; `N` is a closed complement of `K`.
  have := hP.finiteDimensional_ker
  have := hP'.finiteDimensional_ker
  have := hP.finite_coker
  have := hP'.finite_coker
  set K := LinearMap.ker (P : F →ₗ[ℝ] F) ⊔ LinearMap.ker (P' : F →ₗ[ℝ] F) with hK
  obtain ⟨N, hN⟩ := (Submodule.ClosedComplemented.of_finiteDimensional K).exists_isTopCompl
  have : FiniteDimensional ℝ (F ⧸ N) :=
    (Submodule.quotientEquivOfIsCompl N K hN.isCompl.symm).symm.finiteDimensional
  -- `R'' = R(P) ∩ R(P') ∩ N` is closed, of finite codimension, and `R'' ∩ K = 0`.
  set R'' := LinearMap.range (P : F →ₗ[ℝ] F) ⊓ LinearMap.range (P' : F →ₗ[ℝ] F) ⊓ N with hR''
  have hR''c : IsClosed (R'' : Set F) :=
    (hP.isClosed_range.inter hP'.isClosed_range).inter hN.isClosed'
  have : FiniteDimensional ℝ (F ⧸ R'') :=
    (Submodule.CoFG.inf hP.finite_coker hP'.finite_coker).inf ‹_›
  have hdisj : Disjoint K R'' := hN.isCompl.disjoint.mono_right inf_le_right
  -- `C ⊇ K` a complement of `R''`; `P''` the projection onto `R''` along `C`.
  obtain ⟨C, hKC, hC⟩ := hdisj.exists_isCompl
  have htop : Submodule.IsTopCompl R'' C :=
    Submodule.IsCompl.isTopCompl_of_finiteDimensional_quotient hC.symm hR''c
  have hle : ProjLE (R''.projectionL C htop) P :=
    projLE_projectionL htop hP.isProj (le_sup_left.trans hKC) (inf_le_left.trans inf_le_left)
  have hle' : ProjLE (R''.projectionL C htop) P' :=
    projLE_projectionL htop hP'.isProj (le_sup_right.trans hKC) (inf_le_left.trans inf_le_right)
  refine ⟨R''.projectionL C htop, ⟨Submodule.isIdempotentElem_projectionL htop, ?_, ?_⟩, hle, hle'⟩
  · rw [Submodule.range_projectionL]
    assumption
  · exact range_comp_eq_of_comp_eq hP hle.1.symm

/-- **The text's construction in Lemma 6.10, as we read it**: on `F = ℝ²` with `T = 1` there are
`P, P' ∈ Π_T` such that no projection with range `R(P) ∩ R(P')` lies below both. -/
theorem lemma_6_10_text_reading_preprint :
    ∃ P P' : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ),
      IsGoodLeftProj (ContinuousLinearMap.id ℝ (ℝ × ℝ)) P ∧
      IsGoodLeftProj (ContinuousLinearMap.id ℝ (ℝ × ℝ)) P' ∧
      ∀ P'' : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ), P'' ∘L P'' = P'' →
        LinearMap.range (P'' : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) =
          LinearMap.range (P : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) ⊓
            LinearMap.range (P' : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) →
        ¬ (ProjLE P'' P ∧ ProjLE P'' P') := by
  -- `P (x, y) = (x, 0)` (along the `y`-axis), `P' (x, y) = (x − y, 0)` (along the diagonal).
  set P : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    ContinuousLinearMap.inl ℝ ℝ ℝ ∘L ContinuousLinearMap.fst ℝ ℝ ℝ with hPdef
  set P' : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    ContinuousLinearMap.inl ℝ ℝ ℝ ∘L (ContinuousLinearMap.fst ℝ ℝ ℝ -
      ContinuousLinearMap.snd ℝ ℝ ℝ) with hP'def
  have hP : ∀ v, P v = (v.1, 0) := fun v => rfl
  have hP' : ∀ v, P' v = (v.1 - v.2, 0) := fun v => rfl
  refine ⟨P, P', ⟨?_, inferInstance, ?_⟩, ⟨?_, inferInstance, ?_⟩, ?_⟩
  · ext <;> simp [hP]
  · rw [ContinuousLinearMap.comp_id]
  · ext <;> simp [hP']
  · rw [ContinuousLinearMap.comp_id]
  · intro P'' hidem hrange hle
    have hmem : ((-1 : ℝ), (0 : ℝ)) ∈ LinearMap.range (P'' : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) := by
      rw [hrange]
      exact ⟨⟨(-1, 0), by simp [hP]⟩, ⟨(-1, 0), by simp [hP']⟩⟩
    have h1 : P'' ((-1 : ℝ), (0 : ℝ)) = (-1, 0) := proj_apply_eq_self_of_mem_range hidem hmem
    have h2 : P'' ((0 : ℝ), (1 : ℝ)) = 0 := by
      rw [hle.1.1, ContinuousLinearMap.comp_apply, hP]
      exact map_zero P''
    have h3 : P'' ((0 : ℝ), (1 : ℝ)) = (-1, 0) := by
      rw [hle.2.1, ContinuousLinearMap.comp_apply, hP']
      simpa using h1
    have := h2.symm.trans h3
    simp [Prod.ext_iff] at this

end Polyfold
