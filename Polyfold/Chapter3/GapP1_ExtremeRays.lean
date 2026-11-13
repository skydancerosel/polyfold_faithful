import Polyfold.Chapter3.Book2021Items

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §3.8.1.2–3.8.1.3:
**Lemmas 3.8.1–3.8.3** (preprint 3.62–3.64), pp. 145–147: closed convex cones, extreme rays and
quadrants.

# Extreme rays of closed convex cones

## The text, paraphrased

A closed convex cone `P` in a finite-dimensional `N` is a closed convex set with `P ∩ (−P) = {0}`
and `ℝ₊ · P = P`; an extreme ray is `R = ℝ₊ · x`, `x ∈ P ∖ {0}`, such that `y ∈ P`, `x − y ∈ P`
imply `y ∈ R`.  A quadrant is a closed convex cone carried onto `[0, ∞)ⁿ` by a linear isomorphism
`N ≅ ℝⁿ`.  (Lemma 3.8.1, Krein–Milman) `P` is the closed convex hull of its extreme rays.  (Lemma
3.8.2) A closed convex cone with nonempty interior is a quadrant iff it has `dim N` extreme rays.
(Lemma 3.8.3) For `N ⊆ ℝⁿ ⊕ W` finite-dimensional with `N ∩ C` a closed convex cone,
`C = [0, ∞)ⁿ ⊕ W`, and `a` a generator of an extreme ray of `N ∩ C`: `dim N − 1 ≤ #σ_a`
(`σ_a` the indices with `a_i = 0`), with equality if `N` is in good position.

## What is formalized

* `Polyfold.rayOf` (`ℝ₊ · x`), `Polyfold.IsExtremeRay` (an extreme ray as a set),
  `Polyfold.extremeRays`, `Polyfold.IsQuadrantIn`: the text's definitions, next to the project's
  `Polyfold.IsClosedConvexCone` and `Polyfold.IsExtremeRayGen` (`Chapter3/Book2021Items`);
  `IsClosedConvexCone.isExtremeRay_rayOf_iff` identifies the two readings of "generator of an
  extreme ray".
* `Polyfold.IsClosedConvexCone.exists_pos_functional`: a closed convex cone has a functional with
  `φ(x) ≥ c|x|` on `P`, `c > 0` (separation from `−z` for each unit vector `z ∈ P`, compactness of
  the unit sphere of `P`); its base `P ∩ {φ = 1}` is compact and convex.
* `Polyfold.lemma_3_8_1`: **Lemma 3.8.1** for `P ≠ {0}`; by Mathlib's Krein–Milman theorem on the
  base, whose extreme points span extreme rays.  For `P = {0}` there are no extreme rays and the
  closed convex hull of the empty family is empty, so the statement as printed does not hold as we
  read it there (`Polyfold.not_lemma_3_8_1_zero`); with `0` adjoined it holds for every closed
  convex cone (`Polyfold.lemma_3_8_1_zero_union`).
* `Polyfold.extremeRays_nonnegOrthant`: the extreme rays of `[0, ∞)ⁿ` are the `ℝ₊ · e_i`.
* `Polyfold.lemma_3_8_2`: **Lemma 3.8.2** (“`dim N` many” as `encard = dim N`).
* `Polyfold.lemma_3_8_3`, `Polyfold.lemma_3_8_3_goodPosition`: **Lemma 3.8.3**, both assertions,
  in the model `ℝⁿ ⊕ W`, `C = [0, ∞)ⁿ ⊕ W` of the text (`#σ_a` is `quadrantDeg a`).  The good
  position hypothesis enters only through its good complement (the algebraic splitting).
-/

open Set Filter Topology Function Module

set_option linter.unusedSectionVars false

noncomputable section

namespace Polyfold

section Cones

variable {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]

/-- The ray `ℝ₊ · x`. -/
def rayOf (x : N) : Set N := {y | ∃ t : ℝ, 0 ≤ t ∧ y = t • x}

/-- An **extreme ray** of `P` (2021 p. 145): `R = ℝ₊ · x` with `x ∈ P ∖ {0}` such that `y ∈ P` and
`x − y ∈ P` imply `y ∈ R`. -/
def IsExtremeRay (P R : Set N) : Prop :=
  ∃ x ∈ P, x ≠ 0 ∧ R = rayOf x ∧ ∀ y ∈ P, x - y ∈ P → y ∈ R

/-- The set of extreme rays of `P`. -/
def extremeRays (P : Set N) : Set (Set N) := {R | IsExtremeRay P R}

lemma mem_rayOf_self (x : N) : x ∈ rayOf x := ⟨1, zero_le_one, (one_smul ℝ x).symm⟩

lemma zero_mem_rayOf (x : N) : (0 : N) ∈ rayOf x := ⟨0, le_rfl, (zero_smul ℝ x).symm⟩

namespace IsClosedConvexCone

variable {P : Set N} (hP : IsClosedConvexCone P)
include hP

lemma zero_mem : (0 : N) ∈ P := by
  have : (0 : N) ∈ P ∩ -P := by rw [hP.inter_neg]; rfl
  exact this.1

lemma add_mem {x y : N} (hx : x ∈ P) (hy : y ∈ P) : x + y ∈ P := by
  have h := hP.convex hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  have h2 := hP.smul_mem 2 (by norm_num) _ h
  rwa [smul_add, smul_smul, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul,
    one_smul] at h2

lemma rayOf_subset {x : N} (hx : x ∈ P) : rayOf x ⊆ P := by
  rintro _ ⟨t, ht, rfl⟩; exact hP.smul_mem t ht x hx

lemma sum_mem {ι : Type*} (s : Finset ι) {z : ι → N} (hz : ∀ i ∈ s, z i ∈ P) :
    ∑ i ∈ s, z i ∈ P :=
  Finset.sum_induction z (· ∈ P) (fun _ _ => hP.add_mem) hP.zero_mem hz

/-- The union of the extreme rays lies in `P`. -/
lemma sUnion_extremeRays_subset : ⋃₀ extremeRays P ⊆ P := by
  rintro y ⟨R, ⟨x, hx, -, rfl, -⟩, hy⟩
  exact hP.rayOf_subset hx hy

/-- `P` contains the closed convex hull of its extreme rays. -/
lemma closure_convexHull_subset : closure (convexHull ℝ (⋃₀ extremeRays P)) ⊆ P :=
  closure_minimal (convexHull_min hP.sUnion_extremeRays_subset hP.convex) hP.isClosed

/-- A point `z ≠ 0` of `P` is separated from `−P`: a functional `≥ 0` on `P` and `> 0` at `z`. -/
lemma exists_functional_pos {z : N} (hz : z ∈ P) (hz0 : z ≠ 0) :
    ∃ f : N →L[ℝ] ℝ, (∀ b ∈ P, 0 ≤ f b) ∧ 0 < f z := by
  have hdisj : Disjoint ({-z} : Set N) P := by
    rw [disjoint_singleton_left]
    intro h
    exact hz0 (hP.eq_zero hz h)
  obtain ⟨f, u, v, hu, huv, hv⟩ := geometric_hahn_banach_compact_closed (convex_singleton (-z))
    isCompact_singleton hP.convex hP.isClosed hdisj
  have hv0 : v < 0 := by simpa using hv 0 hP.zero_mem
  have hnn : ∀ b ∈ P, 0 ≤ f b := by
    intro b hb
    by_contra hneg'
    have hneg : f b < 0 := not_le.1 hneg'
    have := hv ((v / f b) • b) (hP.smul_mem _ (div_nonneg_of_nonpos hv0.le hneg.le) b hb)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ v hneg.ne] at this
    exact lt_irrefl v this
  refine ⟨f, hnn, ?_⟩
  have h1 := hu (-z) rfl
  rw [map_neg] at h1
  linarith

/-- **A strictly positive functional**: `φ(x) ≥ c|x|` on `P` with `c > 0` (finite dimensions). -/
theorem exists_pos_functional [FiniteDimensional ℝ N] :
    ∃ (φ : N →L[ℝ] ℝ) (c : ℝ), 0 < c ∧ ∀ x ∈ P, c * ‖x‖ ≤ φ x := by
  set S : Set N := P ∩ Metric.sphere 0 1 with hS
  have hScomp : IsCompact S := (isCompact_sphere 0 1).inter_left hP.isClosed
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · -- `P = {0}`
    refine ⟨0, 1, one_pos, fun x hx => ?_⟩
    by_contra hlt'
    have hlt : (0 : N →L[ℝ] ℝ) x < 1 * ‖x‖ := not_le.1 hlt'
    have hx0 : x ≠ 0 := by rintro rfl; simp at hlt
    have : ‖x‖⁻¹ • x ∈ S := ⟨hP.smul_mem _ (inv_nonneg.2 (norm_nonneg x)) x hx, by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 hx0)]⟩
    rw [hSe] at this; exact this
  have hpos : ∀ z ∈ S, ∃ f : N →L[ℝ] ℝ, (∀ b ∈ P, 0 ≤ f b) ∧ 0 < f z := fun z hz =>
    hP.exists_functional_pos hz.1 (ne_zero_of_mem_unit_sphere ⟨z, hz.2⟩)
  choose! g₁ hg₁0 hg₁z using hpos
  classical
  set g : N → N →L[ℝ] ℝ := fun z => if z ∈ S then g₁ z else 0 with hgdef
  have hg0 : ∀ z, ∀ b ∈ P, 0 ≤ g z b := fun z b hb => by
    simp only [hgdef]; split_ifs with h
    · exact hg₁0 z h b hb
    · simp
  have hgz : ∀ z ∈ S, 0 < g z z := fun z hz => by simp only [hgdef, if_pos hz]; exact hg₁z z hz
  obtain ⟨t, hcover⟩ := hScomp.elim_finite_subcover (fun z : N => {x : N | 0 < g z x})
    (fun z => isOpen_lt continuous_const (g z).continuous)
    (fun z hz => mem_iUnion.2 ⟨z, hgz z hz⟩)
  set φ : N →L[ℝ] ℝ := ∑ z ∈ t, g z with hφ
  have hφpos : ∀ x ∈ S, 0 < φ x := by
    intro x hx
    obtain ⟨z, hzt, hzx⟩ := mem_iUnion₂.1 (hcover hx)
    rw [hφ, _root_.sum_apply]
    exact Finset.sum_pos' (fun w _ => hg0 w x hx.1) ⟨z, hzt, hzx⟩
  obtain ⟨z₀, hz₀, hmin⟩ := hScomp.exists_isMinOn hSne φ.continuous.continuousOn
  refine ⟨φ, φ z₀, hφpos z₀ hz₀, fun x hx => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hxS : ‖x‖⁻¹ • x ∈ S := ⟨hP.smul_mem _ (inv_nonneg.2 hn.le) x hx, by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']⟩
  have h := hmin hxS
  simp only [mem_ofPred_eq, map_smul, smul_eq_mul] at h
  calc φ z₀ * ‖x‖ ≤ ‖x‖⁻¹ * φ x * ‖x‖ := by gcongr
    _ = φ x := by field_simp

/-- The extreme points of the base `P ∩ {φ = 1}` span extreme rays of `P`. -/
lemma rayOf_mem_extremeRays {φ : N →L[ℝ] ℝ} {c : ℝ} (hc : 0 < c) (hφ : ∀ x ∈ P, c * ‖x‖ ≤ φ x)
    {e : N} (he : e ∈ (P ∩ φ ⁻¹' {1}).extremePoints ℝ) : rayOf e ∈ extremeRays P := by
  rw [mem_extremePoints] at he
  obtain ⟨⟨heP, he1⟩, hext⟩ := he
  have he1' : φ e = 1 := he1
  have hφnn : ∀ x ∈ P, 0 ≤ φ x := fun x hx => (mul_nonneg hc.le (norm_nonneg x)).trans (hφ x hx)
  have hzero : ∀ x ∈ P, φ x = 0 → x = 0 := fun x hx h0 => by
    have h := hφ x hx
    rw [h0] at h
    exact norm_le_zero_iff.1 (le_of_mul_le_mul_left (by simpa using h) hc)
  refine ⟨e, heP, fun h => by rw [h, map_zero] at he1'; exact zero_ne_one he1', rfl,
    fun y hy hey => ?_⟩
  set s := φ y with hs
  have hs0 : 0 ≤ s := hφnn y hy
  have hs1 : φ (e - y) = 1 - s := by rw [map_sub, he1']
  have hs1' : 0 ≤ 1 - s := hs1 ▸ hφnn _ hey
  rcases hs0.lt_or_eq with hs0 | hs0
  · rcases hs1'.lt_or_eq with hs1'' | hs1''
    · have hy1 : s⁻¹ • y ∈ P ∩ φ ⁻¹' {1} := ⟨hP.smul_mem _ (inv_nonneg.2 hs0.le) y hy, by
        change φ (s⁻¹ • y) = 1
        rw [map_smul, smul_eq_mul, ← hs, inv_mul_cancel₀ hs0.ne']⟩
      have hy2 : (1 - s)⁻¹ • (e - y) ∈ P ∩ φ ⁻¹' {1} :=
        ⟨hP.smul_mem _ (inv_nonneg.2 hs1''.le) _ hey, by
          change φ ((1 - s)⁻¹ • (e - y)) = 1
          rw [map_smul, smul_eq_mul, hs1, inv_mul_cancel₀ hs1''.ne']⟩
      have hseg : e ∈ openSegment ℝ (s⁻¹ • y) ((1 - s)⁻¹ • (e - y)) := by
        refine ⟨s, 1 - s, hs0, hs1'', by ring, ?_⟩
        rw [smul_smul, smul_smul, mul_inv_cancel₀ hs0.ne', mul_inv_cancel₀ hs1''.ne', one_smul,
          one_smul, add_sub_cancel]
      have h := (hext _ hy1 _ hy2 hseg).1
      refine ⟨s, hs0.le, ?_⟩
      rw [← h, smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]
    · -- `φ(e − y) = 0`, so `y = e`
      have : e - y = 0 := hzero _ hey (by rw [hs1, ← hs1''])
      rw [sub_eq_zero] at this
      rw [← this]; exact mem_rayOf_self e
  · -- `φ(y) = 0`, so `y = 0`
    rw [hzero y hy hs0.symm]; exact zero_mem_rayOf e

end IsClosedConvexCone

/-- **Lemma 3.8.1 (preprint 3.62)** (Krein–Milman for cones), 2021 p. 145: a closed convex cone
`P ≠ {0}` in a finite-dimensional space is the closed convex hull of its extreme rays. -/
theorem lemma_3_8_1 [FiniteDimensional ℝ N] {P : Set N} (hP : IsClosedConvexCone P)
    (hne : P ≠ {0}) : P = closure (convexHull ℝ (⋃₀ extremeRays P)) := by
  refine (subset_antisymm ?_ hP.closure_convexHull_subset)
  obtain ⟨φ, c, hc, hφ⟩ := hP.exists_pos_functional
  set B := P ∩ φ ⁻¹' {1} with hB
  have hBclosed : IsClosed B := hP.isClosed.inter (isClosed_singleton.preimage φ.continuous)
  have hBsub : B ⊆ Metric.closedBall 0 (1 / c) := fun x hx => by
    rw [mem_closedBall_zero_iff, le_div_iff₀ hc, mul_comm]
    have h := hφ x hx.1
    rwa [show φ x = 1 from hx.2] at h
  have hBcomp : IsCompact B := (isCompact_closedBall 0 (1 / c)).of_isClosed_subset hBclosed hBsub
  have hBconv : Convex ℝ B := hP.convex.inter ((convex_singleton 1).linear_preimage
    (φ : N →ₗ[ℝ] ℝ))
  have hKM := closure_convexHull_extremePoints hBcomp hBconv
  -- `B` is nonempty, so it has extreme points
  obtain ⟨p, hp, hp0⟩ : ∃ p ∈ P, p ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (Set.eq_singleton_iff_unique_mem.2 ⟨hP.zero_mem, h⟩)
  have hφp : 0 < φ p := (mul_pos hc (norm_pos_iff.2 hp0)).trans_le (hφ p hp)
  have hpB : (φ p)⁻¹ • p ∈ B := ⟨hP.smul_mem _ (inv_nonneg.2 hφp.le) p hp, by
    change φ ((φ p)⁻¹ • p) = 1
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hφp.ne']⟩
  obtain ⟨e, he⟩ : (B.extremePoints ℝ).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, convexHull_empty, closure_empty] at hKM
    rw [← hKM] at hpB; exact hpB
  intro x hx
  rcases eq_or_ne x 0 with rfl | hx0
  · exact subset_closure (subset_convexHull ℝ _
      ⟨rayOf e, hP.rayOf_mem_extremeRays hc hφ he, zero_mem_rayOf e⟩)
  set t := φ x with ht
  have htpos : 0 < t := (mul_pos hc (norm_pos_iff.2 hx0)).trans_le (hφ x hx)
  have hxB : t⁻¹ • x ∈ B := ⟨hP.smul_mem _ (inv_nonneg.2 htpos.le) x hx, by
    change φ (t⁻¹ • x) = 1
    rw [map_smul, smul_eq_mul, ← ht, inv_mul_cancel₀ htpos.ne']⟩
  set L : N →ₗ[ℝ] N := t • LinearMap.id with hL
  have hLc : Continuous L := LinearMap.continuous_of_finiteDimensional L
  have hLx : L (t⁻¹ • x) = x := by
    rw [hL, LinearMap.smul_apply, LinearMap.id_apply, smul_smul, mul_inv_cancel₀ htpos.ne',
      one_smul]
  have hLe : L '' B.extremePoints ℝ ⊆ ⋃₀ extremeRays P := by
    rintro _ ⟨e', he', rfl⟩
    exact ⟨rayOf e', hP.rayOf_mem_extremeRays hc hφ he', t, htpos.le, rfl⟩
  rw [← hKM] at hxB
  have h1 := image_closure_subset_closure_image hLc ⟨_, hxB, hLx⟩
  rw [L.image_convexHull] at h1
  exact closure_mono (convexHull_mono hLe) h1

/-- The cone `{0}` has no extreme rays. -/
lemma extremeRays_zero : extremeRays ({0} : Set N) = ∅ := by
  ext R
  simp only [mem_empty_iff_false, iff_false]
  rintro ⟨x, hx, hx0, -⟩
  exact hx0 hx

lemma isClosedConvexCone_zero : IsClosedConvexCone ({0} : Set N) :=
  ⟨isClosed_singleton, convex_singleton 0, by simp, fun t _ x hx => by
    rw [mem_singleton_iff] at hx ⊢; rw [hx, smul_zero]⟩

/-- **Lemma 3.8.1 at `P = {0}`**: the cone `{0}` (in `ℝ`) has no extreme rays, and the closed
convex hull of the empty family is empty; so the statement as printed does not hold as we read it
for `P = {0}`. -/
theorem not_lemma_3_8_1_zero :
    ¬ ∀ P : Set ℝ, IsClosedConvexCone P → P = closure (convexHull ℝ (⋃₀ extremeRays P)) := by
  intro h
  have := h {0} isClosedConvexCone_zero
  rw [extremeRays_zero, sUnion_empty, convexHull_empty, closure_empty] at this
  exact (singleton_ne_empty (0 : ℝ)) this

/-- **Lemma 3.8.1 with `0` adjoined**: every closed convex cone is the closed convex hull of `0`
and its extreme rays. -/
theorem lemma_3_8_1_zero_union [FiniteDimensional ℝ N] {P : Set N} (hP : IsClosedConvexCone P) :
    P = closure (convexHull ℝ ({0} ∪ ⋃₀ extremeRays P)) := by
  refine subset_antisymm ?_ (closure_minimal (convexHull_min
    (union_subset (singleton_subset_iff.2 hP.zero_mem) hP.sUnion_extremeRays_subset) hP.convex)
    hP.isClosed)
  by_cases hne : P = {0}
  · rw [hne]
    exact (subset_convexHull ℝ _).trans subset_closure |>.trans' subset_union_left
  · calc P = closure (convexHull ℝ (⋃₀ extremeRays P)) := lemma_3_8_1 hP hne
      _ ⊆ _ := closure_mono (convexHull_mono subset_union_right)

/-! ### Quadrants and Lemma 3.8.2 -/

/-- The nonnegative orthant `[0, ∞)ⁿ`. -/
def nonnegOrthant (n : ℕ) : Set (Fin n → ℝ) := {x | ∀ i, 0 ≤ x i}

/-- A **quadrant** in `N` (2021 p. 145): a closed convex cone carried onto `[0, ∞)ⁿ`,
`n = dim N`, by a linear isomorphism `N ≅ ℝⁿ`. -/
def IsQuadrantIn (P : Set N) : Prop :=
  IsClosedConvexCone P ∧
    ∃ T : N ≃ₗ[ℝ] (Fin (finrank ℝ N) → ℝ), T '' P = nonnegOrthant (finrank ℝ N)

lemma rayOf_smul_of_pos {c : ℝ} (hc : 0 < c) (v : N) : rayOf (c • v) = rayOf v := by
  ext y; constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨t * c, mul_nonneg ht hc.le, by rw [mul_smul]⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t / c, div_nonneg ht hc.le, by rw [smul_smul, div_mul_cancel₀ t hc.ne']⟩

section Transport

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]

lemma image_rayOf (T : N ≃ₗ[ℝ] M) (x : N) : T '' rayOf x = rayOf (T x) := by
  ext y; constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩; exact ⟨t, ht, by rw [map_smul]⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨t • x, ⟨t, ht, rfl⟩, by rw [map_smul]⟩

/-- Extreme rays are carried by linear isomorphisms. -/
lemma IsExtremeRay.image (T : N ≃ₗ[ℝ] M) {P R : Set N} (h : IsExtremeRay P R) :
    IsExtremeRay (T '' P) (T '' R) := by
  obtain ⟨x, hx, hx0, rfl, hext⟩ := h
  refine ⟨T x, mem_image_of_mem _ hx, (map_ne_zero_iff _ T.injective).2 hx0, image_rayOf T x, ?_⟩
  rintro _ ⟨y, hy, rfl⟩ hxy
  have hxy' : x - y ∈ P := by
    obtain ⟨z, hz, hzeq⟩ := hxy
    have : z = x - y := T.injective (by rw [hzeq, map_sub])
    rwa [← this]
  exact mem_image_of_mem _ (hext y hy hxy')

lemma extremeRays_image (T : N ≃ₗ[ℝ] M) (P : Set N) :
    extremeRays (T '' P) = (fun R => T '' R) '' extremeRays P := by
  ext R; constructor
  · intro h
    refine ⟨T.symm '' R, ?_, ?_⟩
    · have := IsExtremeRay.image T.symm h
      have hP : T.symm '' (T '' P) = P := by rw [image_image]; simp
      rwa [hP] at this
    · change T '' (T.symm '' R) = R
      rw [image_image]; simp
  · rintro ⟨R', hR', rfl⟩; exact hR'.image T

lemma encard_extremeRays_image (T : N ≃ₗ[ℝ] M) (P : Set N) :
    (extremeRays (T '' P)).encard = (extremeRays P).encard := by
  rw [extremeRays_image, InjOn.encard_image]
  exact (Set.image_injective.2 T.injective).injOn

end Transport

/-- **The extreme rays of `[0, ∞)ⁿ`** are the rays `ℝ₊ · e_i` (2021 p. 145). -/
theorem extremeRays_nonnegOrthant (n : ℕ) :
    extremeRays (nonnegOrthant n) = range fun i : Fin n => rayOf (Pi.single i (1 : ℝ)) := by
  ext R; constructor
  · rintro ⟨x, hx, hx0, rfl, hext⟩
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h; push Not at h; exact hx0 (funext h)
    have hxi : 0 < x i := lt_of_le_of_ne (hx i) (Ne.symm hi)
    have hj : ∀ j, j ≠ i → x j = 0 := by
      intro j hji
      have hy : Pi.single j (x j) ∈ nonnegOrthant n := fun k => by
        by_cases hk : k = j
        · subst hk; simpa using hx k
        · simp [hk]
      have hxy : x - Pi.single j (x j) ∈ nonnegOrthant n := fun k => by
        by_cases hk : k = j
        · subst hk; simp
        · simpa [Pi.single_apply, hk] using hx k
      obtain ⟨t, -, hteq⟩ := hext _ hy hxy
      have h1 := congrFun hteq i
      simp only [Pi.single_apply, Ne.symm hji, if_false, Pi.smul_apply, smul_eq_mul] at h1
      have ht0 : t = 0 := by
        rcases mul_eq_zero.1 h1.symm with h | h
        · exact h
        · exact absurd h hi
      have h2 := congrFun hteq j
      simpa [ht0] using h2
    have hxeq : x = x i • Pi.single i (1 : ℝ) := funext fun k => by
      by_cases hk : k = i
      · subst hk; simp
      · simp [hk, hj k hk]
    refine ⟨i, ?_⟩
    change rayOf (Pi.single i (1 : ℝ)) = rayOf x
    rw [hxeq, rayOf_smul_of_pos hxi]
  · rintro ⟨i, rfl⟩
    refine ⟨Pi.single i 1, fun k => ?_, fun h => by simpa using congrFun h i, rfl, ?_⟩
    · by_cases hk : k = i
      · subst hk; simp
      · simp [hk]
    · intro y hy hxy
      refine ⟨y i, hy i, funext fun k => ?_⟩
      by_cases hk : k = i
      · subst hk; simp
      · have h1 := hy k
        have h2 := hxy k
        simp only [Pi.sub_apply, Pi.single_apply, hk, if_false, zero_sub, neg_nonneg] at h2
        simp [hk, le_antisymm h2 h1]

lemma encard_extremeRays_nonnegOrthant (n : ℕ) : (extremeRays (nonnegOrthant n)).encard = n := by
  rw [extremeRays_nonnegOrthant, ← image_univ, InjOn.encard_image, encard_univ,
    ENat.card_eq_coe_fintype_card, Fintype.card_fin]
  intro i _ j _ hij
  have : (Pi.single i 1 : Fin n → ℝ) ∈ rayOf (Pi.single j 1 : Fin n → ℝ) := by
    simp only at hij; rw [← hij]; exact mem_rayOf_self _
  obtain ⟨t, -, ht⟩ := this
  have h := congrFun ht i
  by_contra hne
  simp [hne] at h

lemma isClosedConvexCone_nonnegOrthant (n : ℕ) : IsClosedConvexCone (nonnegOrthant n) where
  isClosed := by
    have : nonnegOrthant n = ⋂ i, {x : Fin n → ℝ | 0 ≤ x i} := by ext; simp [nonnegOrthant]
    rw [this]; exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  convex := by
    have : nonnegOrthant n = ⋂ i, {x : Fin n → ℝ | 0 ≤ x i} := by ext; simp [nonnegOrthant]
    rw [this]
    exact convex_iInter fun i => convex_halfSpace_ge (LinearMap.proj (R := ℝ) i).isLinear 0
  inter_neg := by
    ext x
    simp only [mem_inter_iff, Set.mem_neg, mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact funext fun i => le_antisymm (by simpa using h2 i) (h1 i)
    · rintro rfl; exact ⟨fun _ => le_rfl, fun _ => by simp⟩
  smul_mem t ht x hx i := mul_nonneg ht (hx i)

/-- **Lemma 3.8.2 (preprint 3.63)**, 2021 p. 145: a closed convex cone `P` with nonempty interior
in a finite-dimensional `N` is a quadrant iff it has `dim N` extreme rays. -/
theorem lemma_3_8_2 [FiniteDimensional ℝ N] {P : Set N} (hP : IsClosedConvexCone P)
    (hint : (interior P).Nonempty) :
    IsQuadrantIn P ↔ (extremeRays P).encard = finrank ℝ N := by
  constructor
  · rintro ⟨-, T, hT⟩
    rw [← encard_extremeRays_image T, hT, encard_extremeRays_nonnegOrthant]
  · intro h
    refine ⟨hP, ?_⟩
    -- enumerate the extreme rays and choose generators
    have hfin := finite_of_encard_eq_coe h
    have hcard : hfin.toFinset.card = finrank ℝ N := by
      rw [hfin.encard_eq_coe_toFinset_card] at h; exact_mod_cast h
    set e := hfin.toFinset.equivFinOfCardEq hcard
    have hR : ∀ i, IsExtremeRay P ((e.symm i : Set N)) := fun i =>
      hfin.mem_toFinset.1 (e.symm i).2
    choose x hxP hx0 hxR hxext using hR
    have hsurj : ∀ R ∈ extremeRays P, ∃ i, R = rayOf (x i) := by
      intro R hRm
      refine ⟨e ⟨R, hfin.mem_toFinset.2 hRm⟩, ?_⟩
      rw [← hxR, Equiv.symm_apply_apply]
    -- the rays span `N`
    set S : Submodule ℝ N := Submodule.span ℝ (range x)
    have hPS : P ⊆ S := by
      rw [lemma_3_8_1_zero_union hP]
      refine closure_minimal (convexHull_min (union_subset ?_ ?_) S.convex)
        (Submodule.closed_of_finiteDimensional S)
      · rw [singleton_subset_iff]; exact S.zero_mem
      · rintro y ⟨R, hRm, hy⟩
        obtain ⟨i, rfl⟩ := hsurj R hRm
        obtain ⟨t, -, rfl⟩ := hy
        exact S.smul_mem t (Submodule.subset_span (mem_range_self i))
    have hStop : S = ⊤ := S.eq_top_of_nonempty_interior' (hint.mono (interior_mono hPS))
    have hli : LinearIndependent ℝ x :=
      linearIndependent_of_top_le_span_of_card_eq_finrank hStop.ge (by simp)
    set b := basisOfLinearIndependentOfCardEqFinrank' x hli (by simp)
    have hb : ⇑b = x := coe_basisOfLinearIndependentOfCardEqFinrank' x hli _
    -- `P` is the preimage of the orthant under the coordinates of `b`
    have hK : P = b.equivFun ⁻¹' nonnegOrthant (finrank ℝ N) := by
      have hcont : Continuous b.equivFun := by
        have := b.equivFun.toContinuousLinearEquiv.continuous; simpa using this
      have hKc : IsClosed (b.equivFun ⁻¹' nonnegOrthant (finrank ℝ N)) :=
        (isClosedConvexCone_nonnegOrthant _).isClosed.preimage hcont
      have hKv : Convex ℝ (b.equivFun ⁻¹' nonnegOrthant (finrank ℝ N)) := by
        have := (isClosedConvexCone_nonnegOrthant (finrank ℝ N)).convex.linear_preimage
          (b.equivFun : N →ₗ[ℝ] _)
        exact this
      refine subset_antisymm ?_ ?_
      · rw [lemma_3_8_1_zero_union hP]
        refine closure_minimal (convexHull_min (union_subset ?_ ?_) hKv) hKc
        · rw [singleton_subset_iff]
          intro k; simp
        · rintro y ⟨R, hRm, hy⟩
          obtain ⟨i, rfl⟩ := hsurj R hRm
          obtain ⟨t, ht, rfl⟩ := hy
          intro k
          rw [← hb, map_smul, Pi.smul_apply, b.equivFun_self, smul_eq_mul]
          exact mul_nonneg ht (by split_ifs <;> norm_num)
      · intro y hy
        rw [← b.sum_equivFun y]
        exact hP.sum_mem _ fun i _ => hP.smul_mem _ (hy i) _ (by rw [hb]; exact hxP i)
    refine ⟨b.equivFun, ?_⟩
    rw [hK, image_preimage_eq _ b.equivFun.surjective]

/-- If `c • a − y ∈ P` with `c > 0`, `y ∈ P` and `a` extremal, then `y ∈ ℝ₊ · a`. -/
lemma IsClosedConvexCone.mem_rayOf_of_smul_sub_mem {P : Set N} (hP : IsClosedConvexCone P)
    {a y : N} (hext : ∀ y ∈ P, a - y ∈ P → y ∈ rayOf a) {c : ℝ} (hc : 0 < c) (hy : y ∈ P)
    (h : c • a - y ∈ P) : y ∈ rayOf a := by
  have h1 := hext (c⁻¹ • y) (hP.smul_mem _ (inv_nonneg.2 hc.le) y hy) (by
    have := hP.smul_mem _ (inv_nonneg.2 hc.le) _ h
    rwa [smul_sub, smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at this)
  obtain ⟨t, ht, hteq⟩ := h1
  refine ⟨c * t, mul_nonneg hc.le ht, ?_⟩
  rw [mul_smul, ← hteq, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]

/-- A generator `a` of an extreme ray `ℝ₊ · a` (as a set) generates an extreme ray in the sense of
`IsExtremeRayGen`. -/
lemma IsClosedConvexCone.isExtremeRayGen_of_isExtremeRay {P : Set N} (hP : IsClosedConvexCone P)
    {a : N} (h : IsExtremeRay P (rayOf a)) : IsExtremeRayGen P a := by
  obtain ⟨x, hxP, hx0, hax, hext⟩ := h
  have hmem : a ∈ rayOf x := hax ▸ mem_rayOf_self a
  obtain ⟨t, ht, rfl⟩ := hmem
  have ht0 : t ≠ 0 := by
    rintro rfl
    have hx : x ∈ rayOf ((0 : ℝ) • x) := by rw [hax]; exact mem_rayOf_self x
    obtain ⟨s, -, hs⟩ := hx
    exact hx0 (by simpa using hs)
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  rw [hax] at hext
  refine ⟨hP.smul_mem t ht x hxP, smul_ne_zero ht0 hx0, fun y hy hay => ?_⟩
  change y ∈ rayOf (t • x)
  rw [rayOf_smul_of_pos htpos]
  exact hP.mem_rayOf_of_smul_sub_mem hext htpos hy hay

lemma isExtremeRay_of_isExtremeRayGen {P : Set N} {a : N} (h : IsExtremeRayGen P a) :
    IsExtremeRay P (rayOf a) :=
  ⟨a, h.1, h.2.1, rfl, h.2.2⟩

/-- The two readings of "`a` generates an extreme ray" agree on closed convex cones. -/
lemma IsClosedConvexCone.isExtremeRay_rayOf_iff {P : Set N} (hP : IsClosedConvexCone P) {a : N} :
    IsExtremeRay P (rayOf a) ↔ IsExtremeRayGen P a :=
  ⟨hP.isExtremeRayGen_of_isExtremeRay, isExtremeRay_of_isExtremeRayGen⟩

end Cones

/-! ### Lemma 3.8.3 -/

section Lemma383

variable {n : ℕ} {W : ScBanach} {N : Submodule ℝ (((ScBanach.const (Fin n → ℝ)).prod W) 0)}

/-- The projection `N → ℝ^{σ_a}`, `σ_a = {i | a_i = 0}`, of (3.34). -/
def zeroIdxProj (N : Submodule ℝ (((ScBanach.const (Fin n → ℝ)).prod W) 0))
    (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0) : N →ₗ[ℝ] ({i // a.1 i = 0} → ℝ) where
  toFun y i := (y : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma card_zeroIdx (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0) :
    Fintype.card {i // a.1 i = 0} = quadrantDeg a := by
  rw [Fintype.card_subtype]; rfl

lemma zeroIdxProj_self (a : N) :
    zeroIdxProj N (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0) a = 0 :=
  funext fun i => i.2

/-- First step of the proof of Lemma 3.8.3: an element of `N ∩ C ∩ (ℝ^{σᶜ} ⊕ W)` lies on the
extreme ray. -/
lemma mem_rayOf_of_zeroIdxProj_eq_zero
    (hP : IsClosedConvexCone (Subtype.val ⁻¹' quadrant n W 0 : Set N)) {a y : N}
    (haC : (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0) ∈ quadrant n W 0)
    (hext : ∀ y ∈ (Subtype.val ⁻¹' quadrant n W 0 : Set N),
      a - y ∈ (Subtype.val ⁻¹' quadrant n W 0 : Set N) → y ∈ rayOf a)
    (hy : (y : ((ScBanach.const (Fin n → ℝ)).prod W) 0) ∈ quadrant n W 0)
    (hQ : zeroIdxProj N (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0) y = 0) : y ∈ rayOf a := by
  set μ := ∑ i, (y : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 i /
    (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 i + 1 with hμdef
  have hsum : 0 ≤ ∑ i, (y : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 i /
      (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 i :=
    Finset.sum_nonneg fun i _ => div_nonneg (hy i) (haC i)
  have hμ : 0 < μ := by linarith
  refine hP.mem_rayOf_of_smul_sub_mem hext hμ hy (fun i => ?_)
  simp only [Submodule.coe_sub, Submodule.coe_smul, Prod.fst_sub, Prod.smul_fst, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  by_cases hai : (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 i = 0
  · have : (y : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 i = 0 := congrFun hQ ⟨i, hai⟩
    rw [hai, this]; simp
  · have hapos := lt_of_le_of_ne (haC i) (Ne.symm hai)
    have h1 := Finset.single_le_sum
      (f := fun j => (y : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 j /
        (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 j)
      (fun j _ => div_nonneg (hy j) (haC j)) (Finset.mem_univ i)
    have h2 : (y : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 i /
        (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 i ≤ μ := by simp only at h1; linarith
    rw [div_le_iff₀ hapos] at h2; linarith

/-- (3.33): `N ∩ (ℝ^{σᶜ} ⊕ W) ⊆ ℝ · a`. -/
lemma ker_zeroIdxProj_le
    (hP : IsClosedConvexCone (Subtype.val ⁻¹' quadrant n W 0 : Set N)) {a : N}
    (haC : (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0) ∈ quadrant n W 0)
    (hext : ∀ y ∈ (Subtype.val ⁻¹' quadrant n W 0 : Set N),
      a - y ∈ (Subtype.val ⁻¹' quadrant n W 0 : Set N) → y ∈ rayOf a) :
    LinearMap.ker (zeroIdxProj N (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0)) ≤
      Submodule.span ℝ {a} := by
  intro z hz
  rw [LinearMap.mem_ker] at hz
  set l := ∑ i, |(z : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 i| /
    (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 i + 1 with hldef
  have hsum : 0 ≤ ∑ i, |(z : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 i| /
      (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 i :=
    Finset.sum_nonneg fun i _ => div_nonneg (abs_nonneg _) (haC i)
  have hw : l • a + z ∈ rayOf a := by
    refine mem_rayOf_of_zeroIdxProj_eq_zero hP haC hext (fun i => ?_) (by
      rw [map_add, map_smul, zeroIdxProj_self, hz, smul_zero, add_zero])
    simp only [Submodule.coe_add, Submodule.coe_smul, Prod.fst_add, Prod.smul_fst, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    by_cases hai : (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 i = 0
    · have : (z : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 i = 0 := congrFun hz ⟨i, hai⟩
      rw [hai, this]; simp
    · have hapos := lt_of_le_of_ne (haC i) (Ne.symm hai)
      have h1 := Finset.single_le_sum
        (f := fun j => |(z : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 j| /
          (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 j)
        (fun j _ => div_nonneg (abs_nonneg _) (haC j)) (Finset.mem_univ i)
      have h2 : |(z : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 i| /
          (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 i ≤ l := by simp only at h1; linarith
      rw [div_le_iff₀ hapos] at h2
      have := neg_abs_le ((z : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 i)
      nlinarith
  obtain ⟨t, -, ht⟩ := hw
  rw [Submodule.mem_span_singleton]
  exact ⟨t - l, by rw [sub_smul, ← ht]; abel⟩

/-- **Lemma 3.8.3 (preprint 3.64), first part**, 2021 p. 146: for `N ⊆ ℝⁿ ⊕ W`
finite-dimensional with `N ∩ C` a closed convex cone, `C = [0, ∞)ⁿ ⊕ W`, and `a` a generator of an
extreme ray of `N ∩ C`: `dim N − 1 ≤ #σ_a` (`#σ_a = quadrantDeg a`). -/
theorem lemma_3_8_3 [FiniteDimensional ℝ N]
    (hP : IsClosedConvexCone (Subtype.val ⁻¹' quadrant n W 0 : Set N)) {a : N}
    (ha : IsExtremeRayGen (Subtype.val ⁻¹' quadrant n W 0 : Set N) a) :
    finrank ℝ N - 1 ≤ quadrantDeg (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0) := by
  obtain ⟨haP, ha0, hext⟩ := ha
  have h1 := LinearMap.finrank_range_add_finrank_ker
    (zeroIdxProj N (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0))
  have h2 : finrank ℝ (LinearMap.range
      (zeroIdxProj N (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0))) ≤
      quadrantDeg (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0) :=
    (Submodule.finrank_le _).trans (by rw [Module.finrank_fintype_fun_eq_card, card_zeroIdx])
  have h3 := (Submodule.finrank_mono (ker_zeroIdxProj_le hP haP hext)).trans_eq
    (finrank_span_singleton ha0)
  omega

/-- **Lemma 3.8.3 (preprint 3.64), second part**, 2021 p. 146: if moreover `N` is in good
position to `C`, then `dim N − 1 = #σ_a`. -/
theorem lemma_3_8_3_goodPosition [FiniteDimensional ℝ N]
    (hP : IsClosedConvexCone (Subtype.val ⁻¹' quadrant n W 0 : Set N)) {a : N}
    (ha : IsExtremeRayGen (Subtype.val ⁻¹' quadrant n W 0 : Set N) a)
    (hN : IsInGoodPosition ((ScBanach.const (Fin n → ℝ)).prod W) (quadrant n W 0) N) :
    finrank ℝ N - 1 = quadrantDeg (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0) := by
  obtain ⟨haP, ha0, hext⟩ := ha
  obtain ⟨P', hc, ε, hε, hgood⟩ := hN.exists_goodComplement
  have ha0' : (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0) ≠ 0 := by simpa using ha0
  -- the good complement lies in `ℝ^{σᶜ} ⊕ W`
  have hvan : ∀ y ∈ P', ∀ i, (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 i = 0 →
      0 ≤ y.1 i := by
    intro y hy i hai
    by_contra hneg
    have hneg' := not_le.1 hneg
    have hy0 : y ≠ 0 := by rintro rfl; simp at hneg'
    have hapos : 0 < ‖(a : ((ScBanach.const (Fin n → ℝ)).prod W) 0)‖ := norm_pos_iff.2 ha0'
    have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy0
    set s := ε * ‖(a : ((ScBanach.const (Fin n → ℝ)).prod W) 0)‖ / ‖y‖
    have hs : 0 < s := by positivity
    have hle : ‖s • y‖ ≤ ε * ‖(a : ((ScBanach.const (Fin n → ℝ)).prod W) 0)‖ := by
      rw [norm_smul, Real.norm_of_nonneg hs.le, div_mul_cancel₀ _ hypos.ne']
    have := ((hgood _ a.2 (s • y) (P'.smul_mem s hy) hle).1 haP) i
    simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hai,
      zero_add] at this
    exact absurd this (not_le.2 (mul_neg_of_pos_of_neg hs hneg'))
  have hzero : ∀ y ∈ P', ∀ i, (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 i = 0 →
      y.1 i = 0 := fun y hy i hai =>
    le_antisymm (by simpa using hvan (-y) (P'.neg_mem hy) i hai) (hvan y hy i hai)
  -- hence the projection (3.34) is onto
  have hsurj :
      LinearMap.range (zeroIdxProj N (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0)) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro k
    set e : ((ScBanach.const (Fin n → ℝ)).prod W) 0 :=
      (fun i => if h : (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 i = 0 then k ⟨i, h⟩ else 0,
        0) with hedef
    have he : e ∈ N ⊔ P' := by rw [hc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 he
    refine ⟨⟨x, hx⟩, funext fun i => ?_⟩
    have h1 := congrArg (fun p : ((ScBanach.const (Fin n → ℝ)).prod W) 0 => p.1 i) hxy
    simp only [Prod.fst_add, Pi.add_apply, hzero y hy i i.2, add_zero] at h1
    change x.1 i = k i
    rw [h1, hedef]
    exact dif_pos i.2
  have h1 := LinearMap.finrank_range_add_finrank_ker
    (zeroIdxProj N (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0))
  rw [hsurj, finrank_top, Module.finrank_fintype_fun_eq_card, card_zeroIdx] at h1
  have h3 := (Submodule.finrank_mono (ker_zeroIdxProj_le hP haP hext)).trans_eq
    (finrank_span_singleton ha0)
  have h4 : 1 ≤ finrank ℝ (LinearMap.ker
      (zeroIdxProj N (a : ((ScBanach.const (Fin n → ℝ)).prod W) 0))) := by
    rw [← finrank_span_singleton (K := ℝ) ha0]
    exact Submodule.finrank_mono (Submodule.span_le.2 (singleton_subset_iff.2
      (LinearMap.mem_ker.2 (zeroIdxProj_self a))))
  omega

end Lemma383

end Polyfold
