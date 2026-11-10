import Polyfold.Chapter4.ManifoldStokes2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021): the boundary points of
degeneracy index `1` of a manifold with corners and their induced orientation (**Definition
9.3.8**, p. 427, outward vector first; **Definition 9.3.10**, p. 428), across charts; the
boundary used in **Theorem 4.4.7** (p. 199, gap G.40) and Theorem 6.7.1 (p. 277).  Numbers and pages
the 2021 text's.

# Chart changes preserve the faces, and the induced orientation

A point `y` of the quadrant `[0,∞)ᵐ` has degeneracy index `1` on the face `{xᵢ = 0}` if `i` is
its only vanishing coordinate (`∀ k, y k = 0 ↔ k = i`).

## What is formalized

* `mem_posTangentConeAt_of_mem_quadrant`, `nonneg_apply_of_hasFDerivWithinAt`: a map of a
  relatively open subset of the quadrant into the quadrant has a derivative mapping the tangent
  cone at `y` into the half-spaces `{w_k ≥ 0}` of the vanishing coordinates `k` of `f(y)`.
* **`exists_face_of_hasFDerivWithinAt`**: a `C¹` diffeomorphism germ of the quadrant maps a point
  of degeneracy index `1` on the face `{xᵢ = 0}` to a point of degeneracy index `1` on a face
  `{x_j = 0}`, its derivative maps the hyperplane `{xᵢ = 0}` into `{x_j = 0}`, and the inward
  vector `eᵢ` to an inward vector (`(A eᵢ)_j > 0`).
* `exists_face_chartChange`: the same for the chart changes of a manifold modelled on the
  quadrant (`chartChangeDeriv`), and `hasFDerivWithinAt_faceTransition`: the face transition
  `π_j ∘ (e' ∘ e⁻¹) ∘ ιᵢ` has derivative `faceRestrict A i j`.
* `ManifoldForm.chartBoundaryIntegral_eq_sum_openQuadrant`: the boundary integral in a chart is
  the integral over the boundary points of degeneracy index `1` (the corners are null).
* **`orientation_face_chartChange`**: the induced orientation of the boundary agrees across
  signed charts: at a boundary point of degeneracy index `1` in the face `i` of the chart `e`
  (signed `b`) and the face `j` of `e'` (signed `b'`), the face transition has
  `sign det = (orSign b · faceSign i)(orSign b' · faceSign j)`, the two readings of the boundary
  orientation (outward vector first) in the face parametrizations
  (`orSign_faceSign_mul_det_faceRestrict_pos`, `ManifoldStokes2021.lean`).
-/

open Set Filter Topology Manifold Module

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- Mathlib's model with corners `[0,∞)ⁿ ⊆ ℝⁿ`. -/
local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

section Cone

variable {m : ℕ}

theorem stdFrame_apply_apply (i k : Fin m) :
    stdFrame m i k = if k = i then 1 else 0 := by
  rw [stdFrame_eq_toLp_single]
  exact Pi.single_apply i 1 k

/-- **The tangent cone of the quadrant**: if `s` is a neighbourhood of `y` within the quadrant,
every `v` with `v_k ≥ 0` at the vanishing coordinates `k` of `y` lies in the positive tangent cone
of `s` at `y`. -/
theorem mem_posTangentConeAt_of_mem_quadrant {s : Set (EuclideanSpace ℝ (Fin m))}
    {y : EuclideanSpace ℝ (Fin m)} (hy : y ∈ closedQuadrant univ)
    (hs : s ∈ 𝓝[closedQuadrant univ] y)
    {v : EuclideanSpace ℝ (Fin m)} (hv : ∀ k, y k = 0 → 0 ≤ v k) :
    v ∈ posTangentConeAt s y := by
  refine mem_posTangentConeAt_of_frequently_mem (Eventually.frequently ?_)
  have hk : ∀ k, ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ (y + t • v) k := fun k => by
    by_cases hyk : y k = 0
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hyk, zero_add]
      exact mul_nonneg (le_of_lt ht) (hv k hyk)
    · have hpos : 0 < y k := lt_of_le_of_ne (hy k (mem_univ k)) (Ne.symm hyk)
      have hc : Continuous fun t : ℝ => (y + t • v) k := by fun_prop
      have := hc.continuousAt (x := 0) |>.eventually (lt_mem_nhds (by simpa using hpos))
      exact (this.filter_mono nhdsWithin_le_nhds).mono fun t ht => ht.le
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), y + t • v ∈ closedQuadrant univ := by
    filter_upwards [eventually_all.2 hk] with t ht k _ using ht k
  have h2 : Tendsto (fun t : ℝ => y + t • v) (𝓝[>] 0) (𝓝[closedQuadrant univ] y) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, h1⟩
    have : Tendsto (fun t : ℝ => y + t • v) (𝓝 0) (𝓝 (y + (0 : ℝ) • v)) := by
      exact tendsto_const_nhds.add (tendsto_id.smul_const v)
    simpa using this.mono_left nhdsWithin_le_nhds
  exact h2 hs

/-- **The derivative of a map into the quadrant on the tangent cone**: if `f` maps a
neighbourhood `s` of `y` within the quadrant into the quadrant and has derivative `A` within `s`
at `y`, then `(A v)_k ≥ 0` for every vanishing coordinate `k` of `f y` and every `v` of the
tangent cone at `y`. -/
theorem nonneg_apply_of_hasFDerivWithinAt {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    {s : Set (EuclideanSpace ℝ (Fin m))} {y : EuclideanSpace ℝ (Fin m)}
    {A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hf : HasFDerivWithinAt f A s y) (hmaps : MapsTo f s (closedQuadrant univ))
    (hy : y ∈ closedQuadrant univ) (hs : s ∈ 𝓝[closedQuadrant univ] y) {k : Fin m} (hk : f y k = 0)
    {v : EuclideanSpace ℝ (Fin m)} (hv : ∀ l, y l = 0 → 0 ≤ v l) : 0 ≤ A v k := by
  have hmin : IsLocalMinOn (fun x => f x k) s y :=
    Filter.eventually_of_mem self_mem_nhdsWithin fun x hx => by
      simp only [hk]; exact hmaps hx k (mem_univ k)
  have hd : HasFDerivWithinAt (fun x => f x k) ((EuclideanSpace.proj (𝕜 := ℝ) k).comp A) s y := by
    have := (EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt.comp_hasFDerivWithinAt y hf
    exact this
  exact hmin.hasFDerivWithinAt_nonneg hd (mem_posTangentConeAt_of_mem_quadrant hy hs hv)

/-- **A diffeomorphism germ of the quadrant preserves the faces at points of degeneracy index
`1`**: let `f` (derivative `A` within `s` at `y`) and `g` (derivative `B` within `t` at `f y`) map
neighbourhoods `s`, `t` of `y`, `f y` within the quadrant into the quadrant, with `g (f y) = y` and
`B = A⁻¹`.  If `i` is the only vanishing coordinate of `y`, then `f y` has exactly one vanishing
coordinate `j`, `A` maps `{xᵢ = 0}` into `{x_j = 0}`, and `(A eᵢ)_j > 0`. -/
theorem exists_face_of_hasFDerivWithinAt
    {f g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    {s t : Set (EuclideanSpace ℝ (Fin m))} {y : EuclideanSpace ℝ (Fin m)}
    {A B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hf : HasFDerivWithinAt f A s y) (hg : HasFDerivWithinAt g B t (f y))
    (hfs : MapsTo f s (closedQuadrant univ)) (hgt : MapsTo g t (closedQuadrant univ))
    (hs : s ∈ 𝓝[closedQuadrant univ] y) (ht : t ∈ 𝓝[closedQuadrant univ] (f y)) (hgf : g (f y) = y)
    (hBA : ∀ v, B (A v) = v) (hAB : ∀ w, A (B w) = w) (hy : y ∈ closedQuadrant univ)
    (hfy : f y ∈ closedQuadrant univ) {i : Fin m} (hi : ∀ k, y k = 0 ↔ k = i) :
    ∃ j, (∀ k, f y k = 0 ↔ k = j) ∧ (∀ v, v i = 0 → A v j = 0) ∧
      0 < A (stdFrame m i) j := by
  set e := stdFrame m
  have he : ∀ a b, e a b = if b = a then 1 else 0 := fun a b => stdFrame_apply_apply a b
  -- (a) `A` maps `{vᵢ = 0}` into `{w_k = 0}` for the vanishing coordinates `k` of `f y`
  have ha : ∀ k, f y k = 0 → ∀ v, v i = 0 → A v k = 0 := fun k hk v hv => by
    have h1 := nonneg_apply_of_hasFDerivWithinAt hf hfs hy hs hk (v := v)
      fun l hl => by rw [(hi l).1 hl, hv]
    have h2 := nonneg_apply_of_hasFDerivWithinAt hf hfs hy hs hk (v := -v)
      fun l hl => by rw [(hi l).1 hl, PiLp.neg_apply, hv, neg_zero]
    rw [map_neg, PiLp.neg_apply] at h2
    linarith
  -- (b) `eᵢ` points inward
  have hb : ∀ k, f y k = 0 → 0 ≤ A (e i) k := fun k hk =>
    nonneg_apply_of_hasFDerivWithinAt hf hfs hy hs hk fun l _ => by
      rw [he]; split_ifs <;> norm_num
  -- the decomposition `v = vᵢ eᵢ + (v - vᵢ eᵢ)`
  have hdec : ∀ v : EuclideanSpace ℝ (Fin m), (v - v i • e i) i = 0 := fun v => by
    simp [he]
  have hAdec : ∀ k, f y k = 0 → ∀ v, A v k = v i * A (e i) k := fun k hk v => by
    have := ha k hk _ (hdec v)
    rw [map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at this
    linarith
  -- (d) `(A eᵢ)_k > 0` for every vanishing coordinate `k` of `f y`
  have hd : ∀ k, f y k = 0 → 0 < A (e i) k := fun k hk => by
    refine lt_of_le_of_ne (hb k hk) fun h0 => ?_
    have := hAdec k hk (B (e k))
    rw [hAB, ← h0, mul_zero, he, if_pos rfl] at this
    exact one_ne_zero this
  -- (c) `f y` has a vanishing coordinate
  obtain ⟨j, hj⟩ : ∃ j, f y j = 0 := by
    by_contra hne
    push Not at hne
    have hgi : g (f y) i = 0 := by rw [hgf]; exact (hi i).2 rfl
    have hBi : ∀ w, B w i = 0 := fun w => by
      have h1 := nonneg_apply_of_hasFDerivWithinAt hg hgt hfy ht hgi (v := w)
        fun l hl => absurd hl (hne l)
      have h2 := nonneg_apply_of_hasFDerivWithinAt hg hgt hfy ht hgi (v := -w)
        fun l hl => absurd hl (hne l)
      rw [map_neg, PiLp.neg_apply] at h2
      linarith
    have := hBi (A (e i))
    rw [hBA, he, if_pos rfl] at this
    exact one_ne_zero this
  refine ⟨j, fun k => ⟨fun hk => ?_, fun hk => hk ▸ hj⟩, ha j hj, hd j hj⟩
  -- (e) uniqueness of the vanishing coordinate
  by_contra hkj
  set w := B (e j)
  have h1 := hAdec k hk w
  rw [hAB, he, if_neg hkj] at h1
  have hwi : w i = 0 := by
    rcases mul_eq_zero.1 h1.symm with h | h
    · exact h
    · exact absurd h (hd k hk).ne'
  have h2 := hAdec j hj w
  rw [hAB, he, if_pos rfl, hwi, zero_mul] at h2
  exact one_ne_zero h2

/-- **The face transition** `π_j ∘ (e' ∘ e⁻¹) ∘ ιᵢ` has the derivative `faceRestrict A i j`
within the face parameter set, `A` the derivative of the chart change. -/
theorem hasFDerivWithinAt_faceTransition {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {A : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))}
    {s : Set (EuclideanSpace ℝ (Fin (n + 1)))} {i j : Fin (n + 1)} {u : EuclideanSpace ℝ (Fin n)}
    (hf : HasFDerivWithinAt f A s (faceEmbedding i u)) :
    HasFDerivWithinAt (faceProjection j ∘ f ∘ faceEmbedding i) (faceRestrict A i j)
      (faceEmbedding i ⁻¹' s) u :=
  (faceProjection j).hasFDerivAt.comp_hasFDerivWithinAt u
    (hf.comp u (faceEmbedding i).hasFDerivWithinAt (mapsTo_preimage _ _))

end Cone

/-! ### Chart changes of a manifold modelled on the quadrant -/

section ChartChange

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant n) M]
  [IsManifold (𝓠 n) ∞ M]

omit [IsManifold (𝓠 n) ∞ M] in
/-- **Chart changes preserve the faces at points of degeneracy index `1`**: if `e(x)` has the
single vanishing coordinate `i`, then `e'(x)` has a single vanishing coordinate `j`, the
derivative `A = D(e' ∘ e⁻¹)(e x)` maps `{xᵢ = 0}` into `{x_j = 0}`, and `(A eᵢ)_j > 0`. -/
theorem exists_face_chartChange {e e' : OpenPartialHomeomorph M (EuclideanQuadrant n)}
    (he : e ∈ IsManifold.maximalAtlas (𝓠 n) ∞ M) (he' : e' ∈ IsManifold.maximalAtlas (𝓠 n) ∞ M)
    {x : M} (hx : x ∈ e.source) (hx' : x ∈ e'.source) {i : Fin n}
    (hi : ∀ k, e.extend (𝓠 n) x k = 0 ↔ k = i) :
    ∃ j, (∀ k, e'.extend (𝓠 n) x k = 0 ↔ k = j) ∧
      (∀ v, v i = 0 → chartChangeDeriv (𝓠 n) e e' x v j = 0) ∧
      0 < chartChangeDeriv (𝓠 n) e e' x (stdFrame n i) j := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hQ := range_modelWithCornersEuclideanQuadrant (m := n)
  have hfx : (𝓠 n).extendCoordChange e e' (e.extend (𝓠 n) x) = e'.extend (𝓠 n) x := by
    simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply]
    rw [e.extend_left_inv hx]
  have hgx : (𝓠 n).extendCoordChange e' e (e'.extend (𝓠 n) x) = e.extend (𝓠 n) x := by
    simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply]
    rw [e'.extend_left_inv hx']
  have hmaps : ∀ (c c' : OpenPartialHomeomorph M (EuclideanQuadrant n)),
      MapsTo ((𝓠 n).extendCoordChange c c') univ (closedQuadrant univ) := fun c c' z _ => by
    rw [← hQ]
    simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply,
      OpenPartialHomeomorph.extend_coe]
    exact mem_range_self _
  have hmem : ∀ (c : OpenPartialHomeomorph M (EuclideanQuadrant n)), c.extend (𝓠 n) x ∈
      closedQuadrant univ := fun c => by
    rw [← hQ, OpenPartialHomeomorph.extend_coe]; exact mem_range_self _
  obtain ⟨j, hj, h1, h2⟩ := exists_face_of_hasFDerivWithinAt
    (s := ((𝓠 n).extendCoordChange e e').source) (t := ((𝓠 n).extendCoordChange e' e).source)
    ((hasFDerivWithinAt_chartChangeDeriv hn he he' hx hx').mono fun z hz => by
        rw [ModelWithCorners.extendCoordChange_source] at hz
        obtain ⟨w, _, rfl⟩ := hz; exact mem_range_self w)
    (by
      rw [hfx]
      exact (hasFDerivWithinAt_chartChangeDeriv hn he' he hx' hx).mono fun z hz => by
        rw [ModelWithCorners.extendCoordChange_source] at hz
        obtain ⟨w, _, rfl⟩ := hz; exact mem_range_self w)
    ((hmaps e e').mono_left (subset_univ _)) ((hmaps e' e).mono_left (subset_univ _))
    (by rw [← hQ]; exact (𝓠 n).extendCoordChange_source_mem_nhdsWithin' hx hx')
    (by rw [hfx, ← hQ]; exact (𝓠 n).extendCoordChange_source_mem_nhdsWithin' hx' hx)
    (by rw [hfx, hgx])
    (fun v => by
      rw [chartChangeDeriv_comp_apply hn he he' he hx hx' hx v, chartChangeDeriv_self hx]; rfl)
    (fun w => by
      rw [chartChangeDeriv_comp_apply hn he' he he' hx' hx hx' w, chartChangeDeriv_self hx']; rfl)
    (hmem e) (by rw [hfx]; exact hmem e') hi
  rw [hfx] at hj
  exact ⟨j, hj, h1, h2⟩

end ChartChange

section Corners

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant (n + 1)) M]

open MeasureTheory in
/-- **The boundary integral over the points of degeneracy index `1`**: in each face parameter set
the corners (points on two faces) form a null set, so the boundary integral in a chart is the sum
of the integrals over `ιᵢ⁻¹(U) ∩ openQuadrant univ`, whose images under `ιᵢ` are the points of
the face `{xᵢ = 0}` with no other vanishing coordinate (`image_faceEmbedding_openQuadrant`), the
points where Definition 9.3.8 orients the boundary. -/
theorem ManifoldForm.chartBoundaryIntegral_eq_sum_openQuadrant
    (e : OpenPartialHomeomorph M (EuclideanQuadrant (n + 1)))
    (ω : ManifoldForm (𝓠 (n + 1)) M n) :
    ManifoldForm.chartBoundaryIntegral e ω = ∑ i : Fin (n + 1), faceSign i *
      topFormIntegral (faceEmbedding i ⁻¹' ((𝓠 (n + 1)).symm ⁻¹' e.target) ∩ openQuadrant univ)
        (facePullback i (ManifoldForm.chartForm (𝓠 (n + 1)) e ω)) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ManifoldForm.extend_target_eq_inter_quadrant, preimage_inter,
    preimage_faceEmbedding_quadrant, Finset.coe_univ, preimage_univ, topFormIntegral,
    topFormIntegral]
  exact congrArg _ (setIntegral_congr_set ((EventuallyEq.refl _ _).inter
    openQuadrant_ae_eq_quadrant).symm)

end Corners

section Orientation

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant (n + 1)) M]
  [IsManifold (𝓠 (n + 1)) ∞ M]

/-- **The induced orientation of the boundary agrees across charts** (Definition 9.3.8, outward
vector first): let `x` be a boundary point of degeneracy index `1`, on the face `{xᵢ = 0}` of the
chart `e`, in which the tangent orientation `o` reads as `signedOr b (stdOrientation (n + 1))`,
and let `e'` be a second chart, reading `o` as `signedOr b' (stdOrientation (n + 1))`.  Then `x`
lies on a single face `{x_j = 0}` of `e'`, and the face transition `π_j ∘ (e' ∘ e⁻¹) ∘ ιᵢ`, with
derivative `faceRestrict A i j` (`hasFDerivWithinAt_faceTransition`), satisfies
`(orSign b · faceSign i) · (orSign b' · faceSign j) · det > 0`: the boundary orientation reads in
the face parametrizations as `orSign b · faceSign i` and `orSign b' · faceSign j`, and the face
transition maps the one to the other. -/
theorem orientation_face_chartChange {o : TangentOrientation (𝓠 (n + 1)) M (n + 1)}
    {e e' : OpenPartialHomeomorph M (EuclideanQuadrant (n + 1))}
    (he : e ∈ IsManifold.maximalAtlas (𝓠 (n + 1)) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas (𝓠 (n + 1)) ∞ M) {x : M} (hx : x ∈ e.source)
    (hx' : x ∈ e'.source) {b b' : Bool}
    (hb : orientationIn e x (o x) = signedOr b (stdOrientation (n + 1)))
    (hb' : orientationIn e' x (o x) = signedOr b' (stdOrientation (n + 1))) {i : Fin (n + 1)}
    (hi : ∀ k, e.extend (𝓠 (n + 1)) x k = 0 ↔ k = i) :
    ∃ j, (∀ k, e'.extend (𝓠 (n + 1)) x k = 0 ↔ k = j) ∧
      0 < orSign b * faceSign i * (orSign b' * faceSign j) *
        (faceRestrict (chartChangeDeriv (𝓠 (n + 1)) e e' x) i j).det := by
  obtain ⟨j, hj, h1, h2⟩ := exists_face_chartChange he he' hx hx' hi
  refine ⟨j, hj, orSign_faceSign_mul_det_faceRestrict_pos (fun u => h1 _ (by simp)) h2
    (orSign_mul_det_chartChangeDeriv_pos he he' hx hx' hb hb')⟩

end Orientation

end Polyfold
