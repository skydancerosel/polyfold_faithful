import Polyfold.Chapter2.TameBoundary

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, Appendix §2.7.4,
**Definition 2.7.11** (p. 82), the map `Φ_{(x,V,θ)}` of (2.44), and **Definition 2.7.6** (p. 79)
for the quadrant `[0,∞)ⁿ ⊕ W`.  Both are new in the 2021 edition.

# (2.44) is not onto `θ` for every `V ∈ N_{X,x}`: an example in `[0,∞)³`

## The text, paraphrased

(Definition 2.7.6) An open `V ⊆ X` is face-structured if every `y ∈ V` lies in exactly `d_X(y)`
faces of `V`; `N_{X,x}` consists of the nonempty face-structured `V ∋ x` on which `d_X` is bounded
and `d_X ≤ d_X(x)`.  (Definition 2.7.11) For `[x, V, θ] ∈ bX`, `U(x, V, θ)` is the set of classes
`[y, V', θ']` with `y ∈ θ`, a morphism `(y, V') → (x, V)` of `L_X`, and `F_X(φ)(θ') = θ`; the
text calls `Φ_{(x,V,θ)} : U(x, V, θ) → θ`, `[y, V', θ'] ↦ y`, the canonical bijection (2.44).

## What is formalized

For the tame M-polyfold `X = [0,∞)ⁿ ⊕ W` (`MPolyfold.quadrantPolyfold n W`), with `d_X = dq n W`:
* `dq_eq`: `d_X(p)` is the number of vanishing half-line coordinates `coord i p`; `part k` is the
  stratum `{p_k = 0, p_l > 0 (l ≠ k)}` and `dq_eq_one_iff`: `{d_X = 1}` is the union of the strata.
* `subset_part`, `faceAt_subset_coord_eq_zero`: a face of an open `V` through a point of `part k`
  lies in the coordinate face `{p_k = 0}`; `exists_part_mem_faceAt`: a point `y` of `V` with
  `y_k = 0` lies on the face of `V` through some point of `V ∩ part k`.
* `isFaceStructuredOpen_quadrant`: **every open subset of `[0,∞)ⁿ ⊕ W` is face-structured**
  (Definition 2.7.6 (1)); so `N_{X,x}` consists of the open `V ∋ x` with `d_X ≤ d_X(x)` on `V`.
* For `n = 3`: `x = (0, 0, 1)` (`pt W 0 0 1`), the thin convex open slab
  `V = {p₀ < 1/2, 1/2 < p₁ + p₂ < 3/2}` around the segment from `x` to `(0, 1, 0)` (`slab`),
  `slab_mem_faceStructuredNbhdsAt` (`V ∈ N_{X,x}`, `d_X(x) = 2`), the face `θ` of `V` through
  the segment (`slabFace`, `seg_mem_slabFace`), and the admissible triple
  `counterTriple W = (x, V, θ)` (Definition 2.7.10).
* `exists_face_not_mem`: `(0, 1, 0) ∈ θ` also lies on the face of `V` in `{p₂ = 0}`, which
  misses `x`; so (`pt_010_not_mem_image`) `(0, 1, 0)` is not in the image `θ ∩ V^x` of `Φ`
  (`bMap_image_uSet`), `phi_not_surjective`, and `not_forall_bijective_phi`: **(2.44)
  does not hold as we read it** for this `V ∈ N_{X,x}`.

## What the text leaves implicit, and the choices made

* `W` is arbitrary; the trivial `W` gives the text's setting `X = [0,∞)³` of the sketch in
  `TameBoundary.lean`.  The coordinates are numbered `0, 1, 2`.
* `Φ_{(x,V,θ)}` is injective for every `V` (`phi_injective`) and a bijection onto `θ` when every
  face of `V` contains `x` (`phi_bijective_of_isCenteredAt`), e.g. for `V^x ∈ N_{X,x}`
  (`reach_mem_faceStructuredNbhdsAt`): the reading "for `V` sufficiently small" formalized in
  `TameBoundary.lean`.  The example shows that some such restriction is needed.
* Membership in `U(x, V, θ)` is "for some representative", as in `TameBoundary.lean`; the example
  does not depend on it, since `Φ` misses `(0, 1, 0)` already on the level of points.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

namespace TameBoundaryExample

open TameBoundary MPolyfold

variable {n : ℕ} {W : ScBanach}

/-- The `i`-th half-line coordinate of a point of `[0,∞)ⁿ ⊕ W`. -/
def coord (i : Fin n) (p : quadrant n W 0) : ℝ := (p : ((ScBanach.const (Fin n → ℝ)).prod W) 0).1 i

lemma coord_nonneg (i : Fin n) (p : quadrant n W 0) : 0 ≤ coord i p := p.2 i

lemma continuous_coord (i : Fin n) : Continuous (coord (W := W) i) :=
  (continuous_apply i).comp (continuous_fst.comp continuous_subtype_val)

/-- The degeneracy index `d_X` of the tame M-polyfold `X = [0,∞)ⁿ ⊕ W` (`quadrantPolyfold`). -/
abbrev dq (n : ℕ) (W : ScBanach) : quadrant n W 0 → ℕ := (quadrantPolyfold n W).degIndex

/-- `d_X` satisfies the corner axioms (`X` is tame). -/
theorem isCornerIndex_dq (n : ℕ) (W : ScBanach) : IsCornerIndex (dq n W) :=
  (quadrantPolyfold n W).isCornerIndex_degIndex (quadrantPolyfold_isTame n W)

/-- `d_X(p)` is the number of vanishing half-line coordinates of `p`. -/
lemma dq_eq (p : quadrant n W 0) :
    dq n W p = (Finset.univ.filter fun i => coord i p = 0).card := by
  rw [dq, quadrantPolyfold, corollary_2_4_13 (isRelOpenInQuadrant_quadrant n W)
    (quadrant_nonempty n W), degIndex_quadrant p.2]
  rfl

/-- The stratum `{p_k = 0, p_l > 0 for l ≠ k}` of the coordinate face `{p_k = 0}`. -/
def part (k : Fin n) : Set (quadrant n W 0) := {p | coord k p = 0 ∧ ∀ l, l ≠ k → 0 < coord l p}

/-- `d_X(p) = 1` iff `p` lies in exactly one coordinate face. -/
lemma dq_eq_one_iff {p : quadrant n W 0} : dq n W p = 1 ↔ ∃ k, p ∈ part k := by
  rw [dq_eq, Finset.card_eq_one]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_, fun l hl => ?_⟩
    · have : k ∈ Finset.univ.filter fun i => coord i p = 0 := by
        rw [hk]; exact Finset.mem_singleton_self k
      exact (Finset.mem_filter.1 this).2
    · have : l ∉ Finset.univ.filter fun i => coord i p = 0 := by rw [hk]; simpa using hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact lt_of_le_of_ne (coord_nonneg l p) (Ne.symm this)
  · rintro ⟨k, hk0, hk⟩
    refine ⟨k, Finset.ext fun l => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hl; by_contra hne; exact (hk l hne).ne' hl
    · rintro rfl; exact hk0

/-- A preconnected subset of `{d_X = 1}` meeting the stratum `part k` lies in it. -/
lemma subset_part {S : Set (quadrant n W 0)} (hS : IsPreconnected S)
    (hS1 : S ⊆ {p | dq n W p = 1}) {k : Fin n} {q : quadrant n W 0} (hqS : q ∈ S)
    (hq : q ∈ part k) : S ⊆ part k := by
  set u : Set (quadrant n W 0) := {p | ∀ l, l ≠ k → 0 < coord l p} with hu_def
  set v : Set (quadrant n W 0) := {p | 0 < coord k p} with hv_def
  have hu : IsOpen u := by
    have : u = ⋂ l, ⋂ (_ : l ≠ k), {p | 0 < coord l p} := by ext p; simp [u]
    rw [this]
    exact isOpen_iInter_of_finite fun l => isOpen_iInter_of_finite fun _ =>
      isOpen_lt continuous_const (continuous_coord l)
  have hv : IsOpen v := isOpen_lt continuous_const (continuous_coord k)
  have hcover : S ⊆ u ∪ v := by
    intro p hp
    obtain ⟨k', -, hk'⟩ := dq_eq_one_iff.1 (hS1 hp)
    by_cases hkk : k' = k
    · subst hkk; exact Or.inl hk'
    · exact Or.inr (hk' k (Ne.symm hkk))
  have hdisj : S ∩ (u ∩ v) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun p ⟨hp, hpu, hpv⟩ => ?_
    obtain ⟨k', hk'0, -⟩ := dq_eq_one_iff.1 (hS1 hp)
    by_cases hkk : k' = k
    · subst hkk; exact hpv.ne' hk'0
    · exact (hpu k' hkk).ne' hk'0
  rcases isPreconnected_iff_subset_of_disjoint.1 hS u v hu hv hcover hdisj with h | h
  · intro p hp
    obtain ⟨k', hk'0, hk'⟩ := dq_eq_one_iff.1 (hS1 hp)
    by_cases hkk : k' = k
    · subst hkk; exact ⟨hk'0, hk'⟩
    · exact absurd hk'0 (h hp k' hkk).ne'
  · exact absurd hq.1 (h hqS).ne'

/-- The face of `V` through a point of `part k` lies in the coordinate face `{p_k = 0}`. -/
lemma faceAt_subset_coord_eq_zero (V : Set (quadrant n W 0)) {k : Fin n} {q : quadrant n W 0}
    (hq : q ∈ part k) : faceAt (dq n W) V q ⊆ {p | coord k p = 0} := by
  refine inter_subset_right.trans
    (closure_minimal ?_ (isClosed_eq (continuous_coord k) continuous_const))
  by_cases hqF : q ∈ V ∩ {p | dq n W p = 1}
  · exact (subset_part isPreconnected_connectedComponentIn
      ((connectedComponentIn_subset _ _).trans inter_subset_right)
      (mem_connectedComponentIn hqF) hq).trans fun p hp => hp.1
  · rw [connectedComponentIn_eq_empty hqF]; exact empty_subset _

/-- Every point `y` of an open `V` with `y_k = 0` lies on the face of `V` through some point of
`V ∩ part k` (approach `y` along `t ↦ y + t Σ_{l ≠ k} e_l`). -/
lemma exists_part_mem_faceAt {V : Set (quadrant n W 0)} (hV : IsOpen V) {y : quadrant n W 0}
    (hy : y ∈ V) {k : Fin n} (hk : coord k y = 0) :
    ∃ q ∈ V, q ∈ part k ∧ y ∈ faceAt (dq n W) V q := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hV y hy
  let c : Fin n → ℝ := fun l => if l = k then 0 else 1
  have hc0 : ∀ l, 0 ≤ c l := fun l => by simp only [c]; split_ifs <;> norm_num
  have hc1 : ∀ l, c l ≤ 1 := fun l => by simp only [c]; split_ifs <;> norm_num
  let γ : ℝ → quadrant n W 0 := fun t =>
    ⟨(((y : (Fin n → ℝ) × W 0).1 + max t 0 • c, (y : (Fin n → ℝ) × W 0).2) :
      (Fin n → ℝ) × W 0), fun i => by
      change 0 ≤ (y : (Fin n → ℝ) × W 0).1 i + max t 0 * c i
      exact add_nonneg (y.2 i) (mul_nonneg (le_max_right t 0) (hc0 i))⟩
  have hγc : ∀ t i, coord i (γ t) = coord i y + max t 0 * c i := fun _ _ => rfl
  have hγ : Continuous γ := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.add ((continuous_id.max continuous_const).smul continuous_const)).prodMk
      continuous_const
  have hγ0 : γ 0 = y := by
    apply Subtype.ext
    change (((y : (Fin n → ℝ) × W 0).1 + max 0 0 • c, (y : (Fin n → ℝ) × W 0).2) :
      (Fin n → ℝ) × W 0) = y
    simp
  have hdist : ∀ t, 0 ≤ t → t < ρ → γ t ∈ V := by
    intro t ht0 htρ
    apply hball
    rw [Metric.mem_ball, Subtype.dist_eq]
    change dist ((((y : (Fin n → ℝ) × W 0).1 + max t 0 • c, (y : (Fin n → ℝ) × W 0).2) :
      (Fin n → ℝ) × W 0)) (y : (Fin n → ℝ) × W 0) < ρ
    rw [Prod.dist_eq, max_lt_iff, dist_self]
    refine ⟨(dist_pi_lt_iff hρ).2 fun i => ?_, hρ⟩
    change dist ((y : (Fin n → ℝ) × W 0).1 i + max t 0 * c i) ((y : (Fin n → ℝ) × W 0).1 i) < ρ
    rw [Real.dist_eq, add_sub_cancel_left,
      max_eq_left ht0, abs_of_nonneg (mul_nonneg ht0 (hc0 i))]
    calc t * c i ≤ t * 1 := mul_le_mul_of_nonneg_left (hc1 i) ht0
      _ < ρ := by rw [mul_one]; exact htρ
  have hpart : ∀ t, 0 < t → γ t ∈ part k := by
    intro t ht
    refine ⟨by rw [hγc, hk]; simp [c], fun l hl => ?_⟩
    rw [hγc, max_eq_left ht.le]
    simp only [c, if_neg hl, mul_one]
    linarith [coord_nonneg l y]
  set S := γ '' Ioo 0 (ρ / 2) with hS
  have hρ2 : 0 < ρ / 2 := half_pos hρ
  have hSsub : S ⊆ V ∩ {p | dq n W p = 1} := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨hdist t ht.1.le (ht.2.trans (half_lt_self hρ)), dq_eq_one_iff.2 ⟨k, hpart t ht.1⟩⟩
  have hqS : γ (ρ / 4) ∈ S := ⟨ρ / 4, ⟨by positivity, by linarith⟩, rfl⟩
  have hScc : S ⊆ connectedComponentIn (V ∩ {p | dq n W p = 1}) (γ (ρ / 4)) :=
    (isPreconnected_Ioo.image γ hγ.continuousOn).subset_connectedComponentIn hqS hSsub
  have hycl : y ∈ closure S := by
    rw [← hγ0]
    refine hγ.continuousWithinAt.mem_closure_image ?_
    rw [closure_Ioo hρ2.ne]
    exact ⟨le_rfl, hρ2.le⟩
  exact ⟨γ (ρ / 4), (hSsub hqS).1, hpart _ (by positivity), hy, closure_mono hScc hycl⟩

/-- **Every open subset of `[0,∞)ⁿ ⊕ W` is face-structured** (2021 Definition 2.7.6 (1)): a point
`y` with `d_X(y)` vanishing coordinates lies on the `d_X(y)` distinct faces of `V` through points
of the strata `part k`, `y_k = 0`. -/
theorem isFaceStructuredOpen_quadrant {V : Set (quadrant n W 0)} (hV : IsOpen V) :
    IsFaceStructuredOpen (dq n W) V := by
  refine ⟨hV, fun y hy => le_antisymm (encard_facesThrough_le (isCornerIndex_dq n W) hV hy) ?_⟩
  have hq : ∀ k, ∃ q, coord k y = 0 → q ∈ V ∧ q ∈ part k ∧ y ∈ faceAt (dq n W) V q := by
    intro k
    by_cases hk : coord k y = 0
    · obtain ⟨q, h1, h2, h3⟩ := exists_part_mem_faceAt hV hy hk
      exact ⟨q, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨y, fun h => absurd h hk⟩
  choose q hq using hq
  have hcard : ((dq n W y : ℕ) : ℕ∞) = ({k | coord k y = 0} : Set (Fin n)).encard := by
    rw [dq_eq, ← Set.encard_coe_eq_coe_finsetCard]; congr 1; ext k; simp
  rw [hcard]
  refine Set.encard_le_encard_of_injOn (f := fun k => faceAt (dq n W) V (q k)) ?_ ?_
  · intro k hk
    obtain ⟨h1, h2, h3⟩ := hq k hk
    exact ⟨isFaceIn_faceAt h1 (dq_eq_one_iff.2 ⟨k, h2⟩), h3⟩
  · intro k hk k' hk' h
    obtain ⟨h1', h2', -⟩ := hq k' hk'
    obtain ⟨-, h2, -⟩ := hq k hk
    by_contra hne
    have hmem : q k' ∈ faceAt (dq n W) V (q k) := by
      simp only at h; rw [h]; exact mem_faceAt_self h1' (dq_eq_one_iff.2 ⟨k', h2'⟩)
    exact (h2'.2 k hne).ne' (faceAt_subset_coord_eq_zero V h2 hmem)

/-! ### The counterexample in `[0,∞)³ ⊕ W` -/

section Three

variable (W)

/-- The point `(max a 0, max b 0, max c 0; 0)` of `[0,∞)³ ⊕ W`. -/
def pt (a b c : ℝ) : quadrant 3 W 0 :=
  ⟨(((![max a 0, max b 0, max c 0] : Fin 3 → ℝ), (0 : W 0)) : (Fin 3 → ℝ) × W 0), by
    intro i; fin_cases i <;> simp⟩

variable {W}

@[simp] lemma coord_pt_zero (a b c : ℝ) : coord 0 (pt W a b c) = max a 0 := rfl
@[simp] lemma coord_pt_one (a b c : ℝ) : coord 1 (pt W a b c) = max b 0 := rfl
@[simp] lemma coord_pt_two (a b c : ℝ) : coord 2 (pt W a b c) = max c 0 := rfl

lemma continuous_pt {f g h : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    Continuous fun t => pt W (f t) (g t) (h t) := by
  refine Continuous.subtype_mk ?_ _
  refine Continuous.prodMk ?_ continuous_const
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact hf.max continuous_const
  · exact hg.max continuous_const
  · exact hh.max continuous_const

/-- In `[0,∞)³ ⊕ W`, `d_X(p)` counts the vanishing coordinates among `p₀, p₁, p₂`. -/
lemma dq_three (p : quadrant 3 W 0) : dq 3 W p =
    (if coord 0 p = 0 then 1 else 0) + (if coord 1 p = 0 then 1 else 0) +
      (if coord 2 p = 0 then 1 else 0) := by
  rw [dq_eq, Finset.card_filter, Fin.sum_univ_three]

variable (W)

/-- The thin convex open slab `V = {p₀ < 1/2, 1/2 < p₁ + p₂ < 3/2}` around the segment from
`(0, 0, 1)` to `(0, 1, 0)`. -/
def slab : Set (quadrant 3 W 0) :=
  {p | coord 0 p < 1 / 2 ∧ 1 / 2 < coord 1 p + coord 2 p ∧ coord 1 p + coord 2 p < 3 / 2}

/-- The segment `t ↦ (0, t, 1 − t)`. -/
def seg (t : ℝ) : quadrant 3 W 0 := pt W 0 t (1 - t)

variable {W}

lemma isOpen_slab : IsOpen (slab W) :=
  (isOpen_lt (continuous_coord 0) continuous_const).inter
    ((isOpen_lt continuous_const ((continuous_coord 1).add (continuous_coord 2))).inter
      (isOpen_lt ((continuous_coord 1).add (continuous_coord 2)) continuous_const))

/-- `d_X ≤ 2` on `V` (`p₁ + p₂ > 0`). -/
lemma dq_le_two {p : quadrant 3 W 0} (hp : p ∈ slab W) : dq 3 W p ≤ 2 := by
  have h := hp.2.1
  rw [dq_three]
  split_ifs with h0 h1 h2 <;> first | (exfalso; linarith) | norm_num

lemma dq_pt_001 : dq 3 W (pt W 0 0 1) = 2 := by
  rw [dq_three]; norm_num

lemma pt_001_mem_slab : pt W 0 0 1 ∈ slab W := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

lemma seg_mem_slab {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : seg W t ∈ slab W := by
  have h1 : max t 0 = t := max_eq_left ht.1
  have h2 : max (1 - t) 0 = 1 - t := max_eq_left (by linarith [ht.2])
  refine ⟨?_, ?_, ?_⟩ <;> simp only [seg, coord_pt_zero, coord_pt_one, coord_pt_two, h1, h2] <;>
    norm_num

lemma dq_seg {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : dq 3 W (seg W t) = 1 := by
  have h1 : max t 0 = t := max_eq_left ht.1.le
  have h2 : max (1 - t) 0 = 1 - t := max_eq_left (by linarith [ht.2])
  rw [dq_three]
  simp [seg, h1, h2, ht.1.ne', show 1 - t ≠ 0 by linarith [ht.2]]

lemma seg_zero : seg W 0 = pt W 0 0 1 := by
  rw [seg, sub_zero]

lemma seg_one : seg W 1 = pt W 0 1 0 := by
  rw [seg, sub_self]

lemma continuous_seg : Continuous (seg W) :=
  continuous_pt continuous_const continuous_id (continuous_const.sub continuous_id)

/-- The segment from `(0, 0, 1)` to `(0, 1, 0)` lies in the closure of the component of
`V ∩ {d_X = 1}` through its midpoint. -/
lemma seg_mem_closure {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    seg W t ∈ closure (connectedComponentIn (slab W ∩ {p | dq 3 W p = 1}) (seg W (1 / 2))) := by
  have hsub : seg W '' Ioo 0 1 ⊆ slab W ∩ {p | dq 3 W p = 1} := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨seg_mem_slab (Ioo_subset_Icc_self hs), dq_seg hs⟩
  have hmid : seg W (1 / 2) ∈ seg W '' Ioo 0 1 := ⟨1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩
  have hcc := (isPreconnected_Ioo.image (seg W) continuous_seg.continuousOn)
    |>.subset_connectedComponentIn hmid hsub
  refine closure_mono hcc (continuous_seg.continuousWithinAt.mem_closure_image ?_)
  rw [closure_Ioo zero_ne_one]
  exact ht

end Three

/-! ### `V ∈ N_{X,x}`, the face `θ`, and the failure of surjectivity -/

section Counterexample

variable (W)

/-- `V ∈ N_{X,x}` for `x = (0, 0, 1)`. -/
theorem slab_mem_faceStructuredNbhdsAt : slab W ∈ faceStructuredNbhdsAt (dq 3 W) (pt W 0 0 1) :=
  ⟨⟨isFaceStructuredOpen_quadrant isOpen_slab, ⟨_, pt_001_mem_slab⟩,
    ⟨2, by rintro _ ⟨p, hp, rfl⟩; exact dq_le_two hp⟩⟩, pt_001_mem_slab,
    fun _ hp => (dq_le_two hp).trans dq_pt_001.ge⟩

/-- The face `θ` of `V` containing the segment from `(0, 0, 1)` to `(0, 1, 0)`. -/
def slabFace : Set (quadrant 3 W 0) := faceAt (dq 3 W) (slab W) (seg W (1 / 2))

lemma isFaceIn_slabFace : IsFaceIn (dq 3 W) (slab W) (slabFace W) :=
  isFaceIn_faceAt (seg_mem_slab ⟨by norm_num, by norm_num⟩) (dq_seg ⟨by norm_num, by norm_num⟩)

lemma seg_mem_slabFace {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : seg W t ∈ slabFace W :=
  ⟨seg_mem_slab ht, seg_mem_closure ht⟩

/-- The admissible triple `(x, V, θ)` (2021 Definition 2.7.10): `x = (0, 0, 1)`, `V` the slab, `θ`
the face of `V` through the segment from `x` to `(0, 1, 0)`. -/
def counterTriple : BTriple (isCornerIndex_dq 3 W) where
  x := pt W 0 0 1
  V := slab W
  mem := slab_mem_faceStructuredNbhdsAt W
  one_le := by rw [dq_pt_001]; norm_num
  θ := slabFace W
  mem_faces := ⟨isFaceIn_slabFace W, by
    rw [← seg_zero]; exact seg_mem_slabFace W ⟨le_rfl, zero_le_one⟩⟩

/-- `(0, 1, 0)` lies on a face of `V` (the one in `{p₂ = 0}`) that misses `x = (0, 0, 1)`. -/
theorem exists_face_not_mem :
    ∃ γ ∈ facesThrough (dq 3 W) (slab W) (pt W 0 1 0), pt W 0 0 1 ∉ γ := by
  have hy : pt W 0 1 0 ∈ slab W := by rw [← seg_one]; exact seg_mem_slab ⟨zero_le_one, le_rfl⟩
  obtain ⟨q, hqV, hq, hyq⟩ := exists_part_mem_faceAt isOpen_slab hy (k := 2) (by simp)
  refine ⟨faceAt (dq 3 W) (slab W) q, ⟨isFaceIn_faceAt hqV (dq_eq_one_iff.2 ⟨2, hq⟩), hyq⟩,
    fun hx => ?_⟩
  have := faceAt_subset_coord_eq_zero (slab W) hq hx
  norm_num at this

/-- `(0, 1, 0) ∈ θ` is not of the form `B([y, V', θ'])` with `[y, V', θ'] ∈ U(x, V, θ)`. -/
theorem pt_010_not_mem_image :
    pt W 0 1 0 ∉ bMap (isCornerIndex_dq 3 W) '' uSet (isCornerIndex_dq 3 W) (counterTriple W) := by
  rw [bMap_image_uSet]
  rintro ⟨-, -, hreach⟩
  obtain ⟨γ, hγ, hxγ⟩ := exists_face_not_mem W
  exact hxγ (hreach γ hγ)

/-- **2021 Definition 2.7.11, (2.44)** (does not hold as we read it): for `x = (0, 0, 1)`,
`V = slab W ∈ N_{X,x}` and the face `θ` of `V` through `x` and `(0, 1, 0)`, the map
`Φ_{(x,V,θ)} : U(x, V, θ) → θ` is not onto `θ`. -/
theorem phi_not_surjective :
    ¬ Surjective (phi (isCornerIndex_dq 3 W) (counterTriple W)) := by
  intro h
  have hyθ : pt W 0 1 0 ∈ (counterTriple W).θ := by
    rw [← seg_one]; exact seg_mem_slabFace W ⟨zero_le_one, le_rfl⟩
  obtain ⟨p, hp⟩ := h ⟨_, hyθ⟩
  exact pt_010_not_mem_image W ⟨p.1, p.2, congrArg Subtype.val hp⟩

/-- The negation of (2.44) for `X = [0,∞)³ ⊕ W`: not every `Φ_{(x,V,θ)}` is a bijection. -/
theorem not_forall_bijective_phi :
    ¬ ∀ t : BTriple (isCornerIndex_dq 3 W), Bijective (phi (isCornerIndex_dq 3 W) t) :=
  fun h => phi_not_surjective W (h _).2

end Counterexample

end TameBoundaryExample

end Polyfold
