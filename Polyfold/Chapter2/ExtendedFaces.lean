import Polyfold.Chapter2.Tame

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §2.5, pp. 52–53 (before
Definition 2.5.1) (preprint §2.4, before Definition 2.33).

# The extended faces of a partial quadrant, intrinsically

## The text, paraphrased

For a partial quadrant `C ⊆ E` (`C ≅ [0,∞)ᵏ ⊕ W`), the set `{e ∈ C | d_C(e) = 1}` has exactly
`k` connected components `A_i`; the smallest linear subspace `f_i` containing `A_i` is an
*extended face*; `H_f` is the closed half-space containing `C` with boundary `f`; for `e ∈ C`,
`F(e) = {f | e ∈ f}` and `d_C(e) = #F(e)`; Definition 2.5.1 sets `C_e = ⋂_{f ∈ F(e)} H_f`.

## What is formalized

Everything is defined from `C` and `d_C` alone (`degIndex`, Definition 1.3.3, independent of the
presentation); a presentation `T : E ≅ ℝⁿ ⊕ W` with `C = T⁻¹([0,∞)ⁿ ⊕ W)` only enters the proofs.

* `faceComponents E C`: the connected components of `{e ∈ C | d_C(e) = 1}`;
  `faceComponents_eq`: they are the sets `A_i = {(Te)_i = 0, (Te)_j > 0 for j ≠ i}`, and
  `ncard_faceComponents`: there are exactly `n` of them.
* `extendedFaces E C`: the spans of the components; `span_faceOpen`: `span A_i` is the hyperplane
  `f_i = {(Te)_i = 0}` (the `E_i` of (2.13)); `ncard_extendedFaces`: exactly `n` extended faces.
* `add_coordFace`: `H_{f_i} := C + f_i` is the half-space `{(Te)_i ≥ 0}` (the `H_i` of (2.14));
  it is closed and contains `C`.
* `ncard_facesAt`: `d_C(e) = #F(e)` for `e ∈ C`.
* `iInter_facesAt`: `⋂_{f ∈ F(e)} (C + f) = C_e`, the partial quadrant of Definition 2.5.1 as
  the library defines it with a presentation (`partialQuadrantAtWith`).
-/

open Set Function Topology
open scoped Pointwise

noncomputable section

namespace Polyfold

namespace GapP1ExtendedFaces

variable {E : ScBanach} {n : ℕ} {W : ScBanach}

/-! ### Intrinsic definitions -/

/-- The boundary points of index one, `{e ∈ C | d_C(e) = 1}`. -/
def stratumOne (E : ScBanach) (C : Set (E 0)) : Set (E 0) := {e | e ∈ C ∧ degIndex E C e = 1}

/-- The connected components of `{e ∈ C | d_C(e) = 1}`. -/
def faceComponents (E : ScBanach) (C : Set (E 0)) : Set (Set (E 0)) :=
  {K | ∃ e ∈ stratumOne E C, K = connectedComponentIn (stratumOne E C) e}

/-- **The extended faces**: the smallest linear subspaces containing the components. -/
def extendedFaces (E : ScBanach) (C : Set (E 0)) : Set (Submodule ℝ (E 0)) :=
  {f | ∃ K ∈ faceComponents E C, f = Submodule.span ℝ K}

/-- `F(e)`: the extended faces containing `e`. -/
def facesAt (E : ScBanach) (C : Set (E 0)) (e : E 0) : Set (Submodule ℝ (E 0)) :=
  {f | f ∈ extendedFaces E C ∧ e ∈ f}

/-! ### The coordinate description -/

variable (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))

/-- The coordinate `e ↦ (Te)_i`. -/
def coordL (i : Fin n) : E 0 →L[ℝ] ℝ :=
  ((ContinuousLinearMap.proj i).comp
    (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (W 0))).comp (T 0 : E 0 →L[ℝ] _)

@[simp] lemma coordL_apply (i : Fin n) (e : E 0) : coordL T i e = (T 0 e).1 i := rfl

/-- The hyperplane `f_i = {(Te)_i = 0}`. -/
def coordFace (i : Fin n) : Submodule ℝ (E 0) := LinearMap.ker (coordL T i : E 0 →ₗ[ℝ] ℝ)

lemma mem_coordFace {i : Fin n} {e : E 0} : e ∈ coordFace T i ↔ (T 0 e).1 i = 0 := Iff.rfl

/-- `A_i = {(Te)_i = 0, (Te)_j > 0 for j ≠ i}`. -/
def faceOpen (i : Fin n) : Set (E 0) := {e | (T 0 e).1 i = 0 ∧ ∀ j, j ≠ i → 0 < (T 0 e).1 j}

/-- The point `T⁻¹(1 − δ_i, 0) ∈ A_i`. -/
def facePoint (i : Fin n) : E 0 := (T 0).symm (fun j => if j = i then 0 else 1, 0)

@[simp] lemma coord_facePoint (i j : Fin n) :
    (T 0 (facePoint T i)).1 j = if j = i then 0 else 1 := by
  simp [facePoint]

lemma facePoint_mem (i : Fin n) : facePoint T i ∈ faceOpen T i :=
  ⟨by rw [coord_facePoint]; simp, fun j hj => by rw [coord_facePoint]; simp [hj]⟩

variable {T}
variable {C : Set (E 0)} (hT : C = T 0 ⁻¹' quadrant n W 0)

include hT in
lemma mem_C_iff {e : E 0} : e ∈ C ↔ ∀ i, 0 ≤ (T 0 e).1 i := by rw [hT]; rfl

include hT in
lemma mem_stratumOne_iff {e : E 0} : e ∈ stratumOne E C ↔ ∃ i, e ∈ faceOpen T i := by
  classical
  constructor
  · rintro ⟨heC, hd⟩
    rw [degIndex_eq T hT heC, degIndexWith, quadrantDeg, Finset.card_eq_one] at hd
    obtain ⟨i, hi⟩ := hd
    have hpos := (mem_C_iff hT).1 heC
    refine ⟨i, ?_, fun j hj => ?_⟩
    · have : i ∈ Finset.univ.filter fun k => (T 0 e).1 k = 0 := by rw [hi]; simp
      simpa using this
    · have hj' : j ∉ Finset.univ.filter fun k => (T 0 e).1 k = 0 := by rw [hi]; simpa using hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj'
      exact lt_of_le_of_ne (hpos j) (Ne.symm hj')
  · rintro ⟨i, hi0, hpos⟩
    have heC : e ∈ C := (mem_C_iff hT).2 fun j => by
      by_cases hj : j = i
      · rw [hj, hi0]
      · exact (hpos j hj).le
    refine ⟨heC, ?_⟩
    rw [degIndex_eq T hT heC, degIndexWith, quadrantDeg, Finset.card_eq_one]
    refine ⟨i, Finset.ext fun j => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hj
      by_contra hji
      exact (hpos j hji).ne' hj
    · rintro rfl; exact hi0

lemma continuous_coord (j : Fin n) : Continuous fun e : E 0 => (T 0 e).1 j :=
  (coordL T j).continuous

lemma convex_faceOpen (i : Fin n) : Convex ℝ (faceOpen T i) := by
  intro e₁ h₁ e₂ h₂ a b ha hb hab
  refine ⟨?_, fun j hj => ?_⟩
  · simp [h₁.1, h₂.1]
  · have hx := h₁.2 j hj
    have hy := h₂.2 j hj
    simp only [map_add, map_smul, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    rcases eq_or_lt_of_le ha with rfl | ha'
    · rw [zero_add] at hab; subst hab; simpa using hy
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' hx) (mul_nonneg hb hy.le)

lemma isOpen_posExcept (i : Fin n) : IsOpen {e : E 0 | ∀ j, j ≠ i → 0 < (T 0 e).1 j} := by
  have : {e : E 0 | ∀ j, j ≠ i → 0 < (T 0 e).1 j} =
      ⋂ j : Fin n, {e : E 0 | j ≠ i → 0 < (T 0 e).1 j} := by ext; simp
  rw [this]
  refine isOpen_iInter_of_finite fun j => ?_
  by_cases hj : j = i
  · simp [hj]
  · simp only [ne_eq, hj, not_false_eq_true, true_implies]
    exact isOpen_lt continuous_const (continuous_coord j)

include hT in
/-- The component of `{d_C = 1}` through a point of `A_i` is `A_i`. -/
theorem connectedComponentIn_eq {i : Fin n} {e : E 0} (he : e ∈ faceOpen T i) :
    connectedComponentIn (stratumOne E C) e = faceOpen T i := by
  have hsub : faceOpen T i ⊆ stratumOne E C := fun e' he' => (mem_stratumOne_iff hT).2 ⟨i, he'⟩
  apply Subset.antisymm _ ((convex_faceOpen i).isPreconnected.subset_connectedComponentIn he hsub)
  set K := connectedComponentIn (stratumOne E C) e
  have hK : IsPreconnected K := isPreconnected_connectedComponentIn
  have hKS : K ⊆ stratumOne E C := connectedComponentIn_subset _ _
  set u := {e : E 0 | ∀ j, j ≠ i → 0 < (T 0 e).1 j}
  set v := {e : E 0 | 0 < (T 0 e).1 i}
  have hsuv : K ⊆ u ∪ v := by
    intro e' he'
    obtain ⟨i', hi'0, hi'⟩ := (mem_stratumOne_iff hT).1 (hKS he')
    by_cases h : i' = i
    · subst h; exact Or.inl hi'
    · exact Or.inr (hi' i (Ne.symm h))
  have hdisj : K ∩ (u ∩ v) = ∅ := by
    ext e'
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro he' hu hv
    obtain ⟨i', hi'0, -⟩ := (mem_stratumOne_iff hT).1 (hKS he')
    by_cases h : i' = i
    · subst h; exact hv.ne' hi'0
    · exact (hu i' h).ne' hi'0
  rcases isPreconnected_iff_subset_of_disjoint.1 hK u v (isOpen_posExcept i)
      (isOpen_lt continuous_const (continuous_coord i)) hsuv hdisj with hKu | hKv
  · intro e' he'
    obtain ⟨i', hi'0, hi'⟩ := (mem_stratumOne_iff hT).1 (hKS he')
    by_cases h : i' = i
    · subst h; exact ⟨hi'0, hi'⟩
    · exact absurd hi'0 (hKu he' i' h).ne'
  · exact absurd he.1 (hKv (mem_connectedComponentIn (hsub he))).ne'

include hT in
/-- **The components of `{d_C = 1}` are the `A_i`.** -/
theorem faceComponents_eq : faceComponents E C = range (faceOpen T) := by
  ext K
  constructor
  · rintro ⟨e, he, rfl⟩
    obtain ⟨i, hi⟩ := (mem_stratumOne_iff hT).1 he
    exact ⟨i, (connectedComponentIn_eq hT hi).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨facePoint T i, (mem_stratumOne_iff hT).2 ⟨i, facePoint_mem T i⟩,
      (connectedComponentIn_eq hT (facePoint_mem T i)).symm⟩

lemma faceOpen_injective : Injective (faceOpen T) := by
  intro i j h
  have := (h ▸ facePoint_mem T i : facePoint T i ∈ faceOpen T j).1
  rw [coord_facePoint] at this
  by_contra hij
  simp [Ne.symm hij] at this

include hT in
/-- **`{d_C = 1}` has exactly `n` connected components** (the text's `k`). -/
theorem ncard_faceComponents : (faceComponents E C).ncard = n := by
  rw [faceComponents_eq hT, ncard_range_of_injective faceOpen_injective, Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- **The smallest linear subspace containing `A_i` is the hyperplane `f_i`.** -/
theorem span_faceOpen (i : Fin n) : Submodule.span ℝ (faceOpen T i) = coordFace T i := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro e he
    exact he.1
  · intro v hv
    set c : ℝ := 1 + ∑ j, |(T 0 v).1 j|
    have hc : ∀ j, |(T 0 v).1 j| < c := fun j => by
      have := Finset.single_le_sum (f := fun j => |(T 0 v).1 j|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ j)
      simp only [c]; linarith
    have hvp : v + c • facePoint T i ∈ faceOpen T i := by
      refine ⟨?_, fun j hj => ?_⟩
      · change (T 0 (v + c • facePoint T i)).1 i = 0
        rw [map_add, map_smul, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
          coord_facePoint, (mem_coordFace T).1 hv]
        simp
      · change 0 < (T 0 (v + c • facePoint T i)).1 j
        rw [map_add, map_smul, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
          coord_facePoint, if_neg hj, smul_eq_mul, mul_one]
        have := hc j
        have := neg_abs_le ((T 0 v).1 j)
        linarith
    have h1 : v + c • facePoint T i ∈ Submodule.span ℝ (faceOpen T i) := Submodule.subset_span hvp
    have h2 : c • facePoint T i ∈ Submodule.span ℝ (faceOpen T i) :=
      Submodule.smul_mem _ _ (Submodule.subset_span (facePoint_mem T i))
    have := Submodule.sub_mem _ h1 h2
    rwa [add_sub_cancel_right] at this

lemma coordFace_injective : Injective (coordFace T) := by
  intro i j h
  have hp : facePoint T i ∈ coordFace T j := h ▸ (facePoint_mem T i).1
  rw [mem_coordFace, coord_facePoint] at hp
  by_contra hij
  simp [Ne.symm hij] at hp

include hT in
/-- **The extended faces are the hyperplanes `f_i`.** -/
theorem extendedFaces_eq : extendedFaces E C = range (coordFace T) := by
  ext f
  simp only [extendedFaces, faceComponents_eq hT, mem_range, exists_exists_eq_and,
    mem_ofPred_eq, span_faceOpen]
  exact ⟨fun ⟨i, h⟩ => ⟨i, h.symm⟩, fun ⟨i, h⟩ => ⟨i, h.symm⟩⟩

include hT in
/-- **There are exactly `n` extended faces.** -/
theorem ncard_extendedFaces : (extendedFaces E C).ncard = n := by
  rw [extendedFaces_eq hT, ncard_range_of_injective coordFace_injective, Nat.card_eq_fintype_card,
    Fintype.card_fin]

include hT in
/-- **The half-space `H_{f_i} = C + f_i` is `{(Te)_i ≥ 0}`** (the `H_i` of (2.14)). -/
theorem add_coordFace (i : Fin n) :
    C + (coordFace T i : Set (E 0)) = {e | 0 ≤ (T 0 e).1 i} := by
  classical
  ext e
  constructor
  · rintro ⟨c, hc, f, hf, rfl⟩
    have h1 := (mem_C_iff hT).1 hc i
    have h2 : (T 0 f).1 i = 0 := hf
    simp only [mem_ofPred_eq, map_add, Prod.fst_add, Pi.add_apply, h2, add_zero]
    exact h1
  · intro he
    set c : E 0 := (T 0).symm (fun j => if j = i then (T 0 e).1 i else 0, (T 0 e).2)
    have hc : c ∈ C := (mem_C_iff hT).2 fun j => by
      simp only [c, ContinuousLinearEquiv.apply_symm_apply]
      split_ifs with hj
      · subst hj; exact he
      · exact le_rfl
    refine ⟨c, hc, e - c, ?_, add_sub_cancel _ _⟩
    change (T 0 (e - c)).1 i = 0
    simp [c]

include hT in
lemma isClosed_add_coordFace (i : Fin n) : IsClosed (C + (coordFace T i : Set (E 0))) := by
  rw [add_coordFace hT]
  exact isClosed_le continuous_const (continuous_coord i)

lemma subset_add_coordFace (i : Fin n) : C ⊆ C + (coordFace T i : Set (E 0)) :=
  fun e he => ⟨e, he, 0, Submodule.zero_mem _, add_zero e⟩

include hT in
lemma facesAt_eq (e : E 0) : facesAt E C e = coordFace T '' {i | (T 0 e).1 i = 0} := by
  ext f
  simp only [facesAt, extendedFaces_eq hT, mem_ofPred_eq, mem_range, mem_image]
  constructor
  · rintro ⟨⟨i, rfl⟩, he⟩; exact ⟨i, he, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, rfl⟩, hi⟩

include hT in
/-- **`d_C(e) = #F(e)`** for `e ∈ C`. -/
theorem ncard_facesAt {e : E 0} (he : e ∈ C) : (facesAt E C e).ncard = degIndex E C e := by
  classical
  rw [facesAt_eq hT, ncard_image_of_injective _ coordFace_injective, degIndex_eq T hT he,
    degIndexWith, quadrantDeg]
  have : {i | (T 0 e).1 i = 0} = ↑(Finset.univ.filter fun i => (T 0 e).1 i = 0) := by
    ext; simp
  rw [this, ncard_coe_finset]

include hT in
/-- **Definition 2.5.1, intrinsically**: `C_e = ⋂_{f ∈ F(e)} H_f` with `H_f = C + f`, which is the
partial quadrant `C_e` of the library (`partialQuadrantAtWith`). -/
theorem iInter_facesAt (e : E 0) :
    ⋂ f ∈ facesAt E C e, C + (f : Set (E 0)) = partialQuadrantAtWith T e := by
  ext v
  simp only [mem_iInter₂, facesAt_eq hT, mem_image, mem_ofPred_eq]
  constructor
  · intro h i hi
    have := h _ ⟨i, hi, rfl⟩
    rw [add_coordFace hT] at this
    exact this
  · rintro h _ ⟨i, hi, rfl⟩
    rw [add_coordFace hT]
    exact h i hi

end GapP1ExtendedFaces

end Polyfold
