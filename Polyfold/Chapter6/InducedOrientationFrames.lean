import Polyfold.Chapter4.StokesFaceOrientation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.4,
**Theorem 4.4.7** (Stokes, p. 199: "`∂N` … equipped with the induced orientation"), with the rule
"outward normal first" of Definition 9.3.8 (p. 427), as used in the proof of Theorem 6.7.1
(p. 278).

# The induced orientation from one frame at each point

`M` is a manifold modelled on `[0,∞)ⁿ⁺¹`, `N` one modelled on `[0,∞)ⁿ` and `j : N → M`
differentiable.  `IsInducedOrientation j o o_N` (`StokesFaceOrientation`) is a statement about all
face chart pairs of `j`.  Here it is derived from one frame at each point, read in the charts
`chartAt` of `N` and `M`, with the outward (or inward) direction detected by a function
`g : M → ℝ` with a local maximum along `j(N)`, constant on `j(N)`:

* `FaceChartPair.chartChangeDeriv_mfderiv`: in a face chart pair `(e_N, e, i)`,
  `D(e ∘ κ'⁻¹) ∘ Tj = ιᵢ ∘ D(e_N ∘ κ⁻¹)` (`κ`, `κ'` the charts at `p`, `j p`).
* `FaceChartPair.exists_derivIn_eq_mul_coord`: if `g ∘ j` is constant near `p` and `g` has a local
  maximum at `j p`, then `dg(w) = c · (D(e ∘ κ'⁻¹) w)ᵢ` with `c ≤ 0`: a vector with `dg(w) > 0`
  points out of `M` (its `i`-th coordinate in `e` is negative), one with `dg(w) < 0` into `M`.
* `signMap_eq_signedOr_of_frame`: the linear algebra (`det(w, ιᵢ v₁, …, ιᵢ vₙ) = −wᵢ · faceSign i ·
  det v`).
* **`isInducedOrientation_of_outward_frames`**: if at every `p` there are bases `b` of `ℝⁿ` and
  `b' = (w, Tj b₁, …, Tj bₙ)` of `ℝⁿ⁺¹` with `dg(w) > 0` and `b'` positive for `o` iff `b` is
  positive for `o_N`, then `o_N` is the induced orientation;
  **`isInducedOrientation_neg_of_inward_frames`**: with `dg(w) < 0` instead, `−o_N` is.
* `derivIn_comp_mfderiv`: the chain rule `T(h ∘ j) = Th ∘ Tj` for `h : M → F`, read in the charts
  `chartAt`.
-/

open Set Filter Topology Manifold Module

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- Mathlib's model with corners `[0,∞)ⁿ ⊆ ℝⁿ`. -/
local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

/-! ### Linear algebra -/

section FrameLinAlg

variable {m n : ℕ}

/-- The orientation of a basis of `ℝᵐ` is `±` the standard one, the sign that of its
determinant. -/
theorem orientation_eq_signedOr_det (b : Basis (Fin m) ℝ (EuclideanSpace ℝ (Fin m))) :
    b.orientation = signedOr (decide (0 < (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.det b))
      (stdOrientation m) := by
  by_cases h : 0 < (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.det b
  · rw [decide_eq_true h, signedOr_true]
    exact ((Basis.orientation_eq_iff_det_pos _ _).2 h).symm
  · rw [decide_eq_false h, signedOr_false]
    have hne : b.orientation ≠ stdOrientation m := fun h' =>
      h ((Basis.orientation_eq_iff_det_pos _ _).1 h'.symm)
    exact (b.orientation.eq_or_eq_neg (stdOrientation m) (by simp)).resolve_left hne

theorem signedOr_inj {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*} {c c' : Bool}
    (ρ : Orientation ℝ E ι) : signedOr c ρ = signedOr c' ρ ↔ c = c' := by
  constructor
  · intro h
    cases c <;> cases c'
    · rfl
    · exact absurd h.symm (Module.Ray.ne_neg_self ρ)
    · exact absurd h (Module.Ray.ne_neg_self ρ)
    · rfl
  · rintro rfl
    rfl

theorem signMap_signedOr_eq {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    {ι : Type*} (A : E →L[ℝ] E) (c : Bool) (ρ : Orientation ℝ E ι) :
    signMap A (signedOr c ρ) = signedOr (c == decide (0 < A.det)) ρ := by
  by_cases h : 0 < A.det
  · rw [signMap_of_pos h, decide_eq_true h]
    cases c <;> rfl
  · unfold signMap
    rw [if_neg h, decide_eq_false h]
    cases c
    · exact neg_neg ρ
    · rfl

open Classical in
theorem decide_signedOr_eq_std (c : Bool) :
    decide (signedOr c (stdOrientation m) = stdOrientation m) = c := by
  cases c
  · exact decide_eq_false fun h => Module.Ray.ne_neg_self (stdOrientation m) h.symm
  · exact decide_eq_true rfl

theorem decide_pos_mul {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    decide (0 < x * y) = (decide (0 < x) == decide (0 < y)) := by
  rcases hx.lt_or_gt with hx' | hx' <;> rcases hy.lt_or_gt with hy' | hy'
  · rw [decide_eq_true (mul_pos_of_neg_of_neg hx' hy'), decide_eq_false (not_lt.2 hx'.le),
      decide_eq_false (not_lt.2 hy'.le)]; rfl
  · rw [decide_eq_false (not_lt.2 (mul_neg_of_neg_of_pos hx' hy').le),
      decide_eq_false (not_lt.2 hx'.le), decide_eq_true hy']; rfl
  · rw [decide_eq_false (not_lt.2 (mul_neg_of_pos_of_neg hx' hy').le), decide_eq_true hx',
      decide_eq_false (not_lt.2 hy'.le)]; rfl
  · rw [decide_eq_true (mul_pos hx' hy'), decide_eq_true hx', decide_eq_true hy']; rfl

theorem faceBool_eq_decide_pos (i : Fin (n + 1)) : faceBool i = decide (0 < faceSign i) := by
  unfold faceBool
  rcases neg_one_pow_eq_or ℝ ((i : ℕ) + 1) with h | h
  · have h' : faceSign i = 1 := h
    rw [h', decide_eq_true rfl, decide_eq_true one_pos]
  · have h' : faceSign i = -1 := h
    rw [h', decide_eq_false (by norm_num), decide_eq_false (by norm_num)]

/-- `det(−eᵢ, ιᵢ v₁, …, ιᵢ vₙ) = faceSign i · det v` (standard bases). -/
theorem det_cons_neg_stdFrame_faceEmbedding (i : Fin (n + 1))
    (v : Fin n → EuclideanSpace ℝ (Fin n)) :
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.det
        (Fin.cons (-stdFrame (n + 1) i) (faceEmbedding i ∘ v)) =
      faceSign i * (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det v := by
  set b₁ := (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis
  set b₀ := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  set f : EuclideanSpace ℝ (Fin n) [⋀^Fin n]→ₗ[ℝ] ℝ :=
    (b₁.det.curryLeft (-stdFrame (n + 1) i)).compLinearMap
      (faceEmbedding i : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
  have hf : ∀ w, f w = b₁.det (Fin.cons (-stdFrame (n + 1) i) (faceEmbedding i ∘ w)) :=
    fun w => rfl
  have h := congrArg (fun g : EuclideanSpace ℝ (Fin n) [⋀^Fin n]→ₗ[ℝ] ℝ => g v)
    (f.eq_smul_basis_det b₀)
  simp only [AlternatingMap.smul_apply, smul_eq_mul] at h
  rw [← hf, h, hf, coe_basisFun_toBasis, det_cons_neg_stdFrame_faceFrame]

/-- **`det(w, ιᵢ v₁, …, ιᵢ vₙ) = −wᵢ · faceSign i · det v`**: the part of `w` in the face
`{xᵢ = 0}` does not contribute. -/
theorem det_cons_faceEmbedding (i : Fin (n + 1)) (w : EuclideanSpace ℝ (Fin (n + 1)))
    (v : Fin n → EuclideanSpace ℝ (Fin n)) :
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.det (Fin.cons w (faceEmbedding i ∘ v)) =
      -(w i) * faceSign i * (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det v := by
  set b₁ := (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis
  set y := faceProjection i (w - w i • stdFrame (n + 1) i)
  have hw : w = w i • stdFrame (n + 1) i + faceEmbedding i y := by
    rw [faceEmbedding_faceProjection (by simp [stdFrame_apply_apply])]
    abel
  have hc : ∀ u, b₁.det (Fin.cons u (faceEmbedding i ∘ v)) =
      b₁.det.curryLeft u (faceEmbedding i ∘ v) := fun u => rfl
  have h0 : b₁.det.curryLeft (faceEmbedding i y) (faceEmbedding i ∘ v) = 0 := by
    rw [← hc, ← Fin.comp_cons]
    refine AlternatingMap.map_linearDependent _ _ fun hli => ?_
    have hli' := LinearIndependent.of_comp
      (faceEmbedding i : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) hli
    have := hli'.fintype_card_le_finrank
    simp at this
  have hneg' : b₁.det (Fin.cons (stdFrame (n + 1) i) (faceEmbedding i ∘ v)) =
      -(faceSign i * (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det v) := by
    rw [← det_cons_neg_stdFrame_faceEmbedding i v, hc, hc, map_neg,
      AlternatingMap.neg_apply, neg_neg]
  conv_lhs => rw [hw]
  rw [hc, map_add, map_smul, AlternatingMap.add_apply, AlternatingMap.smul_apply, h0, add_zero,
    smul_eq_mul, ← hc, hneg']
  ring

open Classical in
/-- **Outward vector first, for one frame**: let `A`, `C` be invertible, `b`, `b'` bases with
`A b'_{l+1} = ιᵢ (C b_l)`, and `b'` positive for `ρ` iff `b` is positive for `σ`.  Then
`C_* σ` is the orientation Part I's rule assigns to the face `{xᵢ = 0}` for `A_* ρ`
(`FaceChartPair.boundarySign`) if `(A b'₀)ᵢ < 0` (outward), its opposite if `(A b'₀)ᵢ > 0`. -/
theorem signMap_eq_signedOr_of_frame (A : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
    EuclideanSpace ℝ (Fin (n + 1))) (C : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : A.det ≠ 0) (hC : C.det ≠ 0) (i : Fin (n + 1))
    (bb : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (bb' : Basis (Fin (n + 1)) ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    (hface : ∀ l, A (bb' l.succ) = faceEmbedding i (C (bb l)))
    {ρ : Orientation ℝ (EuclideanSpace ℝ (Fin (n + 1))) (Fin (n + 1))}
    {σ : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)}
    (h : bb'.orientation = ρ ↔ bb.orientation = σ) (ha : A (bb' 0) i ≠ 0) :
    signMap C σ = signedOr ((decide (signMap A ρ = stdOrientation (n + 1)) == faceBool i) ==
      decide (A (bb' 0) i < 0)) (stdOrientation n) := by
  set b₁ := (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis
  set b₀ := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hcomp : ⇑A ∘ ⇑bb' = Fin.cons (A (bb' 0)) (faceEmbedding i ∘ (⇑C ∘ ⇑bb)) := by
    funext l
    refine Fin.cases ?_ (fun l => ?_) l
    · rfl
    · simp only [Function.comp_apply, Fin.cons_succ, hface]
  have hdet : A.det * b₁.det bb' = -(A (bb' 0) i) * faceSign i * (C.det * b₀.det bb) := by
    have h1 := b₁.det_comp (A : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] _) bb'
    have h2 := b₀.det_comp (C : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] _) bb
    change b₁.det (⇑A ∘ ⇑bb') = A.det * b₁.det bb' at h1
    change b₀.det (⇑C ∘ ⇑bb) = C.det * b₀.det bb at h2
    rw [← h1, ← h2, hcomp, det_cons_faceEmbedding]
  have hD' : b₁.det bb' ≠ 0 := (Basis.isUnit_det _ bb').ne_zero
  have hD : b₀.det bb ≠ 0 := (Basis.isUnit_det _ bb).ne_zero
  have hfs : faceSign i ≠ 0 := pow_ne_zero _ (by norm_num)
  have hB := congrArg (fun x : ℝ => decide (0 < x)) hdet
  simp only at hB
  rw [decide_pos_mul hA hD', decide_pos_mul (mul_ne_zero (neg_ne_zero.2 ha) hfs)
    (mul_ne_zero hC hD), decide_pos_mul (neg_ne_zero.2 ha) hfs, decide_pos_mul hC hD,
    ← faceBool_eq_decide_pos, show decide (0 < -A (bb' 0) i) = decide (A (bb' 0) i < 0) from
      decide_eq_decide.2 neg_pos] at hB
  rw [orientation_eq_signedOr_det bb', orientation_eq_signedOr_det bb,
    eq_signedOr_decide ρ, eq_signedOr_decide σ, signedOr_inj, signedOr_inj] at h
  rw [eq_signedOr_decide ρ, eq_signedOr_decide σ, signMap_signedOr_eq, signMap_signedOr_eq,
    decide_signedOr_eq_std, signedOr_inj]
  revert hB h
  generalize decide (0 < A.det) = pA
  generalize decide (0 < b₁.det bb') = pD'
  generalize decide (A (bb' 0) i < 0) = pa
  generalize faceBool i = pf
  generalize decide (0 < C.det) = pC
  generalize decide (0 < b₀.det bb) = pD
  generalize decide (ρ = stdOrientation (n + 1)) = dρ
  generalize decide (σ = stdOrientation n) = dσ
  decide +revert

end FrameLinAlg

/-! ### Face chart pairs and derivatives -/

section FrameCharts

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant (n + 1)) M]
  [IsManifold (𝓠 (n + 1)) ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanQuadrant n) N] [IsManifold (𝓠 n) ∞ N]
  {j : N → M}

omit [IsManifold (𝓠 (n + 1)) ∞ M] [IsManifold (𝓠 n) ∞ N] in
/-- **The chain rule in the charts at `p` and `j p`**: for `h : M → F` differentiable in the chart
at `j p`, `T(h ∘ j)(p) = Th(j p) ∘ Tj(p)`. -/
theorem derivIn_comp_mfderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {h : M → F}
    {p : N} (hj : MDifferentiableAt (𝓠 n) (𝓠 (n + 1)) j p)
    (hh : DifferentiableWithinAt ℝ (h ∘ ((chartAt (EuclideanQuadrant (n + 1)) (j p)).extend
      (𝓠 (n + 1))).symm) (range (𝓠 (n + 1)))
      ((chartAt (EuclideanQuadrant (n + 1)) (j p)).extend (𝓠 (n + 1)) (j p)))
    (v : EuclideanSpace ℝ (Fin n)) :
    derivIn (𝓠 n) (chartAt (EuclideanQuadrant n) p) (h ∘ j) p v =
      derivIn (𝓠 (n + 1)) (chartAt (EuclideanQuadrant (n + 1)) (j p)) h (j p)
        (mfderiv (𝓠 n) (𝓠 (n + 1)) j p v) := by
  set κ := chartAt (EuclideanQuadrant n) p
  set κ' := chartAt (EuclideanQuadrant (n + 1)) (j p)
  have hW : HasFDerivWithinAt (writtenInExtChartAt (𝓠 n) (𝓠 (n + 1)) p j)
      (mfderiv (𝓠 n) (𝓠 (n + 1)) j p) (range (𝓠 n)) (extChartAt (𝓠 n) p p) := by
    rw [hj.mfderiv]
    exact hj.differentiableWithinAt_writtenInExtChartAt.hasFDerivWithinAt
  have hval : writtenInExtChartAt (𝓠 n) (𝓠 (n + 1)) p j (extChartAt (𝓠 n) p p) =
      κ'.extend (𝓠 (n + 1)) (j p) := by
    simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_to_inv]
    rfl
  have hmaps : MapsTo (writtenInExtChartAt (𝓠 n) (𝓠 (n + 1)) p j) (range (𝓠 n))
      (range (𝓠 (n + 1))) := fun u _ => by
    simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_coe]
    exact mem_range_self _
  have hh' : HasFDerivWithinAt (h ∘ (κ'.extend (𝓠 (n + 1))).symm)
      (derivIn (𝓠 (n + 1)) κ' h (j p)) (range (𝓠 (n + 1)))
      (writtenInExtChartAt (𝓠 n) (𝓠 (n + 1)) p j (extChartAt (𝓠 n) p p)) := by
    rw [hval]; exact hh.hasFDerivWithinAt
  have hcomp := hh'.comp (extChartAt (𝓠 n) p p) hW hmaps
  have hev : (h ∘ j) ∘ (κ.extend (𝓠 n)).symm =ᶠ[𝓝[range (𝓠 n)] (κ.extend (𝓠 n) p)]
      (h ∘ (κ'.extend (𝓠 (n + 1))).symm) ∘ writtenInExtChartAt (𝓠 n) (𝓠 (n + 1)) p j := by
    have hs := κ.extend_preimage_mem_nhds (I := 𝓠 n) (mem_chart_source _ p)
      (hj.continuousAt.preimage_mem_nhds (κ'.open_source.mem_nhds (mem_chart_source _ (j p))))
    filter_upwards [nhdsWithin_le_nhds hs] with u hu
    simp only [Function.comp_apply, writtenInExtChartAt]
    rw [show extChartAt (𝓠 (n + 1)) (j p) = κ'.extend (𝓠 (n + 1)) from rfl,
      show (extChartAt (𝓠 n) p).symm = (κ.extend (𝓠 n)).symm from rfl,
      κ'.extend_left_inv hu]
  have hd : HasFDerivWithinAt ((h ∘ j) ∘ (κ.extend (𝓠 n)).symm)
      ((derivIn (𝓠 (n + 1)) κ' h (j p)).comp (mfderiv (𝓠 n) (𝓠 (n + 1)) j p)) (range (𝓠 n))
      (κ.extend (𝓠 n) p) :=
    hcomp.congr_of_eventuallyEq hev (hev.eq_of_nhdsWithin (by
      rw [OpenPartialHomeomorph.extend_coe]; exact mem_range_self _))
  have hfd : fderivWithin ℝ ((h ∘ j) ∘ (κ.extend (𝓠 n)).symm) (range (𝓠 n))
      (κ.extend (𝓠 n) p) = (derivIn (𝓠 (n + 1)) κ' h (j p)).comp
        (mfderiv (𝓠 n) (𝓠 (n + 1)) j p :
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :=
    HasFDerivWithinAt.fderivWithin hd ((𝓠 n).uniqueDiffOn _ (by
      rw [OpenPartialHomeomorph.extend_coe]; exact mem_range_self _))
  exact congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] F => L v) hfd

namespace FaceChartPair

variable (P : FaceChartPair n j)

/-- **The derivative of `j` in a face chart pair**: `D(e ∘ κ'⁻¹) ∘ Tj = ιᵢ ∘ D(e_N ∘ κ⁻¹)` at
`p`, `κ`, `κ'` the charts at `p` and `j p`: `e ∘ j = ιᵢ ∘ e_N`. -/
theorem chartChangeDeriv_mfderiv {p : N} (hp : p ∈ P.eN.source)
    (hj : MDifferentiableAt (𝓠 n) (𝓠 (n + 1)) j p) (v : EuclideanSpace ℝ (Fin n)) :
    chartChangeDeriv (𝓠 (n + 1)) (chartAt (EuclideanQuadrant (n + 1)) (j p)) P.e (j p)
        (mfderiv (𝓠 n) (𝓠 (n + 1)) j p v) =
      faceEmbedding P.i (chartChangeDeriv (𝓠 n) (chartAt (EuclideanQuadrant n) p) P.eN p v) := by
  set κ := chartAt (EuclideanQuadrant n) p
  set κ' := chartAt (EuclideanQuadrant (n + 1)) (j p)
  have hjpe : j p ∈ P.e.source := P.mapsTo p hp
  have hjpk : j p ∈ κ'.source := mem_chart_source _ (j p)
  have hpk : p ∈ κ.source := mem_chart_source _ p
  have hu₀ : κ.extend (𝓠 n) p ∈ range (𝓠 n) := by
    rw [OpenPartialHomeomorph.extend_coe]; exact mem_range_self _
  have hW : HasFDerivWithinAt (writtenInExtChartAt (𝓠 n) (𝓠 (n + 1)) p j)
      (mfderiv (𝓠 n) (𝓠 (n + 1)) j p) (range (𝓠 n)) (extChartAt (𝓠 n) p p) := by
    rw [hj.mfderiv]
    exact hj.differentiableWithinAt_writtenInExtChartAt.hasFDerivWithinAt
  have hval : writtenInExtChartAt (𝓠 n) (𝓠 (n + 1)) p j (extChartAt (𝓠 n) p p) =
      κ'.extend (𝓠 (n + 1)) (j p) := by
    simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_to_inv]
    rfl
  have hmaps : MapsTo (writtenInExtChartAt (𝓠 n) (𝓠 (n + 1)) p j) (range (𝓠 n))
      (range (𝓠 (n + 1))) := fun u _ => by
    simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_coe]
    exact mem_range_self _
  have hA := hasFDerivWithinAt_chartChangeDeriv (I := 𝓠 (n + 1)) (n := ∞) (by simp)
    (IsManifold.chart_mem_maximalAtlas (j p)) P.mem_M hjpk hjpe
  rw [← hval] at hA
  have h1 := hA.comp (extChartAt (𝓠 n) p p) hW hmaps
  have hC := hasFDerivWithinAt_chartChangeDeriv (I := 𝓠 n) (n := ∞) (by simp)
    (IsManifold.chart_mem_maximalAtlas p) P.mem_N hpk hp
  have h2 := (faceEmbedding P.i).hasFDerivAt.comp_hasFDerivWithinAt _ hC
  have hev1 : (P.e.extend (𝓠 (n + 1)) ∘ j ∘ (κ.extend (𝓠 n)).symm)
      =ᶠ[𝓝[range (𝓠 n)] (κ.extend (𝓠 n) p)]
      (𝓠 (n + 1)).extendCoordChange κ' P.e ∘ writtenInExtChartAt (𝓠 n) (𝓠 (n + 1)) p j := by
    have hs := κ.extend_preimage_mem_nhds (I := 𝓠 n) hpk
      (hj.continuousAt.preimage_mem_nhds (κ'.open_source.mem_nhds hjpk))
    filter_upwards [nhdsWithin_le_nhds hs] with u hu
    simp only [Function.comp_apply, writtenInExtChartAt, ModelWithCorners.extendCoordChange,
      PartialEquiv.coe_trans]
    rw [show extChartAt (𝓠 (n + 1)) (j p) = κ'.extend (𝓠 (n + 1)) from rfl,
      show (extChartAt (𝓠 n) p).symm = (κ.extend (𝓠 n)).symm from rfl,
      κ'.extend_left_inv hu]
  have hev2 : (P.e.extend (𝓠 (n + 1)) ∘ j ∘ (κ.extend (𝓠 n)).symm)
      =ᶠ[𝓝[range (𝓠 n)] (κ.extend (𝓠 n) p)]
      faceEmbedding P.i ∘ (𝓠 n).extendCoordChange κ P.eN := by
    have hs := κ.extend_preimage_mem_nhds (I := 𝓠 n) hpk (P.eN.open_source.mem_nhds hp)
    filter_upwards [nhdsWithin_le_nhds hs] with u hu
    simp only [Function.comp_apply, ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans]
    exact P.extend_eq _ hu
  have h1' := h1.congr_of_eventuallyEq hev1 (hev1.eq_of_nhdsWithin hu₀)
  have h2' := h2.congr_of_eventuallyEq hev2 (hev2.eq_of_nhdsWithin hu₀)
  have := ((𝓠 n).uniqueDiffOn _ hu₀).eq h1' h2'
  exact congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) => L v) this

omit [IsManifold (𝓠 n) ∞ N] in
/-- **Outward and inward vectors from a function with a local maximum on `j(N)`**: if `g ∘ j` is
constant near `p`, `g` has a local maximum at `j p` and is differentiable in the chart `κ'` at
`j p`, then `dg(w) = c · (D(e ∘ κ'⁻¹) w)ᵢ` for some `c ≤ 0`. -/
theorem exists_derivIn_eq_mul_coord {p : N} (hp : p ∈ P.eN.source) {g : M → ℝ}
    (hgmax : IsLocalMax g (j p)) (hgj : ∀ᶠ q in 𝓝 p, g (j q) = g (j p))
    (hgd : DifferentiableWithinAt ℝ (g ∘ ((chartAt (EuclideanQuadrant (n + 1)) (j p)).extend
      (𝓠 (n + 1))).symm) (range (𝓠 (n + 1)))
      ((chartAt (EuclideanQuadrant (n + 1)) (j p)).extend (𝓠 (n + 1)) (j p))) :
    ∃ c ≤ 0, ∀ w, derivIn (𝓠 (n + 1)) (chartAt (EuclideanQuadrant (n + 1)) (j p)) g (j p) w =
      c * chartChangeDeriv (𝓠 (n + 1)) (chartAt (EuclideanQuadrant (n + 1)) (j p)) P.e (j p) w
        P.i := by
  have hy₀ : P.e.extend (𝓠 (n + 1)) (j p) ∈ range (𝓠 (n + 1)) := by
    rw [OpenPartialHomeomorph.extend_coe]; exact mem_range_self _
  set κ' := chartAt (EuclideanQuadrant (n + 1)) (j p)
  set y₀ := P.e.extend (𝓠 (n + 1)) (j p)
  set Dg := derivIn (𝓠 (n + 1)) κ' g (j p)
  set B := chartChangeDeriv (𝓠 (n + 1)) P.e κ' (j p)
  set A := chartChangeDeriv (𝓠 (n + 1)) κ' P.e (j p)
  have hjpe : j p ∈ P.e.source := P.mapsTo p hp
  have hjpk : j p ∈ κ'.source := mem_chart_source _ (j p)
  -- `G = g ∘ e⁻¹` has the derivative `dg ∘ D(κ' ∘ e⁻¹)` at `y₀`
  have hG : HasFDerivWithinAt (g ∘ (P.e.extend (𝓠 (n + 1))).symm) (Dg.comp B)
      (range (𝓠 (n + 1))) y₀ := by
    have h2 := hasFDerivWithinAt_chartChangeDeriv (I := 𝓠 (n + 1)) (n := ∞) (by simp) P.mem_M
      (IsManifold.chart_mem_maximalAtlas (j p)) hjpe hjpk
    have hval : (𝓠 (n + 1)).extendCoordChange P.e κ' y₀ = κ'.extend (𝓠 (n + 1)) (j p) := by
      simp only [y₀, ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans,
        Function.comp_apply]
      rw [P.e.extend_left_inv hjpe]
    have hmaps : MapsTo ((𝓠 (n + 1)).extendCoordChange P.e κ') (range (𝓠 (n + 1)))
        (range (𝓠 (n + 1))) := fun y _ => by
      simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply,
        OpenPartialHomeomorph.extend_coe]
      exact mem_range_self _
    have h1 : HasFDerivWithinAt (g ∘ (κ'.extend (𝓠 (n + 1))).symm) Dg (range (𝓠 (n + 1)))
        ((𝓠 (n + 1)).extendCoordChange P.e κ' y₀) := by
      rw [hval]; exact hgd.hasFDerivWithinAt
    have h3 := h1.comp y₀ h2 hmaps
    have hev : g ∘ (P.e.extend (𝓠 (n + 1))).symm =ᶠ[𝓝[range (𝓠 (n + 1))] y₀]
        (g ∘ (κ'.extend (𝓠 (n + 1))).symm) ∘ (𝓠 (n + 1)).extendCoordChange P.e κ' := by
      have hs := P.e.extend_preimage_mem_nhds (I := 𝓠 (n + 1)) hjpe
        (κ'.open_source.mem_nhds hjpk)
      filter_upwards [nhdsWithin_le_nhds hs] with y hy
      simp only [Function.comp_apply, ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans]
      rw [κ'.extend_left_inv hy]
    exact h3.congr_of_eventuallyEq hev (hev.eq_of_nhdsWithin hy₀)
  -- `dG` vanishes on the face
  have hface : ∀ y, (Dg.comp B) (faceEmbedding P.i y) = 0 := by
    have hu₀ : P.eN.extend (𝓠 n) p ∈ range (𝓠 n) := by
      rw [OpenPartialHomeomorph.extend_coe]; exact mem_range_self _
    set u₀ := P.eN.extend (𝓠 n) p
    have hy₀' : y₀ = faceEmbedding P.i u₀ := P.extend_eq p hp
    rw [hy₀'] at hG
    have hd := hG.comp u₀ (faceEmbedding P.i).hasFDerivWithinAt
      (mapsTo_faceEmbedding_range P.i)
    have h0 : (g ∘ (P.e.extend (𝓠 (n + 1))).symm) ∘ faceEmbedding P.i
        =ᶠ[𝓝[range (𝓠 n)] u₀] fun _ => g (j p) := by
      filter_upwards [P.eN.extend_target_mem_nhdsWithin (I := 𝓠 n) hp,
        nhdsWithin_le_nhds (P.eN.extend_preimage_mem_nhds (I := 𝓠 n) hp hgj)] with u hu hu'
      simp only [Function.comp_apply]
      rw [P.symm_eq hu]
      exact hu'
    have hd0 : HasFDerivWithinAt ((g ∘ (P.e.extend (𝓠 (n + 1))).symm) ∘ faceEmbedding P.i)
        (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (range (𝓠 n)) u₀ :=
      (hasFDerivWithinAt_const (g (j p)) _ _).congr_of_eventuallyEq h0 (h0.eq_of_nhdsWithin hu₀)
    have := ((𝓠 n).uniqueDiffOn _ hu₀).eq hd hd0
    intro y
    exact congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L y) this
  -- `dG(eᵢ) ≤ 0`: `G` has a local maximum on the quadrant at `y₀`
  have hmax : (Dg.comp B) (stdFrame (n + 1) P.i) ≤ 0 := by
    have hloc : IsLocalMaxOn (g ∘ (P.e.extend (𝓠 (n + 1))).symm) (range (𝓠 (n + 1))) y₀ := by
      have hs := P.e.extend_preimage_mem_nhds (I := 𝓠 (n + 1)) hjpe hgmax
      filter_upwards [nhdsWithin_le_nhds hs] with y hy
      simp only [Function.comp_apply, y₀]
      rw [P.e.extend_left_inv hjpe]
      exact hy
    refine hloc.hasFDerivWithinAt_nonpos hG (mem_posTangentConeAt_of_segment_subset ?_)
    rw [range_modelWithCornersEuclideanQuadrant] at hy₀ ⊢
    rintro z ⟨a, b, ha, hb, -, rfl⟩ l -
    have h1 := hy₀ l (mem_univ _)
    have h2 : 0 ≤ stdFrame (n + 1) P.i l := by
      rw [stdFrame_apply_apply]; split_ifs <;> norm_num
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    positivity
  refine ⟨_, hmax, fun w => ?_⟩
  have hinv := chartChangeDeriv_comp_self (I := 𝓠 (n + 1)) (n := ∞) (by simp)
    (IsManifold.chart_mem_maximalAtlas (j p)) P.mem_M hjpk hjpe
  have hBA : B (A w) = w := by
    have := congrArg (fun L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)) => L w) hinv
    simpa using this
  have hdec : A w = A w P.i • stdFrame (n + 1) P.i +
      faceEmbedding P.i (faceProjection P.i (A w - A w P.i • stdFrame (n + 1) P.i)) := by
    rw [faceEmbedding_faceProjection (by simp [stdFrame_apply_apply])]
    abel
  have := congrArg (Dg.comp B) hdec
  rw [map_add, map_smul, hface, add_zero, smul_eq_mul] at this
  rw [ContinuousLinearMap.comp_apply, hBA] at this
  rw [this, mul_comm]

end FaceChartPair

/-! ### The induced orientation -/

variable (o : TangentOrientation (𝓠 (n + 1)) M (n + 1)) (oN : TangentOrientation (𝓠 n) N n)

open Classical in
/-- At one point, in one face chart pair: the reading of `o_N` from a frame. -/
theorem FaceChartPair.orientationIn_eq_of_frame (P : FaceChartPair n j) {p : N}
    (hp : p ∈ P.eN.source) (hj : MDifferentiableAt (𝓠 n) (𝓠 (n + 1)) j p) {g : M → ℝ}
    (hgmax : IsLocalMax g (j p)) (hgj : ∀ᶠ q in 𝓝 p, g (j q) = g (j p))
    (hgd : DifferentiableWithinAt ℝ (g ∘ ((chartAt (EuclideanQuadrant (n + 1)) (j p)).extend
      (𝓠 (n + 1))).symm) (range (𝓠 (n + 1)))
      ((chartAt (EuclideanQuadrant (n + 1)) (j p)).extend (𝓠 (n + 1)) (j p)))
    (bb : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (bb' : Basis (Fin (n + 1)) ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    (hsucc : ∀ l, bb' l.succ = mfderiv (𝓠 n) (𝓠 (n + 1)) j p (bb l))
    (hne : derivIn (𝓠 (n + 1)) (chartAt (EuclideanQuadrant (n + 1)) (j p)) g (j p) (bb' 0) ≠ 0)
    (hor : bb'.orientation = tangentOrToModel (o (j p)) ↔
      bb.orientation = tangentOrToModel (oN p)) :
    orientationIn P.eN p (oN p) = signedOr (P.boundarySign o p ==
      decide (0 < derivIn (𝓠 (n + 1)) (chartAt (EuclideanQuadrant (n + 1)) (j p)) g (j p)
        (bb' 0))) (stdOrientation n) := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hjpe : j p ∈ P.e.source := P.mapsTo p hp
  have hA := det_chartChangeDeriv_ne_zero hn (IsManifold.chart_mem_maximalAtlas (j p)) P.mem_M
    (mem_chart_source _ (j p)) hjpe
  have hC := det_chartChangeDeriv_ne_zero hn (IsManifold.chart_mem_maximalAtlas p) P.mem_N
    (mem_chart_source _ p) hp
  obtain ⟨c, hc, hcw⟩ := P.exists_derivIn_eq_mul_coord hp hgmax hgj hgd
  have hw := hcw (bb' 0)
  set a := chartChangeDeriv (𝓠 (n + 1)) (chartAt (EuclideanQuadrant (n + 1)) (j p)) P.e (j p)
    (bb' 0) P.i
  have ha : a ≠ 0 := fun h0 => hne (by rw [hw, h0, mul_zero])
  have hsign : decide (a < 0) = decide (0 < derivIn (𝓠 (n + 1))
      (chartAt (EuclideanQuadrant (n + 1)) (j p)) g (j p) (bb' 0)) := by
    rw [hw]
    refine decide_eq_decide.2 ⟨fun h => mul_pos_of_neg_of_neg ?_ h, fun h => ?_⟩
    · rcases hc.lt_or_eq with hc' | hc'
      · exact hc'
      · exact absurd (by rw [hw, hc', zero_mul]) hne
    · by_contra h'
      have : c * a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (not_lt.1 h')
      linarith
  have key := signMap_eq_signedOr_of_frame _ _ hA hC P.i bb bb'
    (fun l => by rw [hsucc l]; exact P.chartChangeDeriv_mfderiv hp hj (bb l)) hor ha
  unfold orientationIn FaceChartPair.boundarySign
  rw [key, ← hsign]
  rfl

/-- **The induced orientation from outward frames**: if at every `p ∈ N` there are bases `b` of
`ℝⁿ` and `b' = (w, Tj b₁, …, Tj bₙ)` of `ℝⁿ⁺¹` (read in the charts at `p` and `j p`) with
`dg(w) > 0`, `g` a function with a local maximum along `j(N)` and constant on `j(N)`, such that
`b'` is positive for `o` iff `b` is positive for `o_N`, then `o_N` is the orientation induced by
`j` (outward vector first). -/
theorem isInducedOrientation_of_outward_frames
    (hj : ∀ p, MDifferentiableAt (𝓠 n) (𝓠 (n + 1)) j p) {g : M → ℝ}
    (hgmax : ∀ p, IsLocalMax g (j p)) (hgj : ∀ p, ∀ᶠ q in 𝓝 p, g (j q) = g (j p))
    (hgd : ∀ p, DifferentiableWithinAt ℝ (g ∘ ((chartAt (EuclideanQuadrant (n + 1)) (j p)).extend
      (𝓠 (n + 1))).symm) (range (𝓠 (n + 1)))
      ((chartAt (EuclideanQuadrant (n + 1)) (j p)).extend (𝓠 (n + 1)) (j p)))
    (hfr : ∀ p, ∃ (bb : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
      (bb' : Basis (Fin (n + 1)) ℝ (EuclideanSpace ℝ (Fin (n + 1)))),
      (∀ l, bb' l.succ = mfderiv (𝓠 n) (𝓠 (n + 1)) j p (bb l)) ∧
      0 < derivIn (𝓠 (n + 1)) (chartAt (EuclideanQuadrant (n + 1)) (j p)) g (j p) (bb' 0) ∧
      (bb'.orientation = tangentOrToModel (o (j p)) ↔
        bb.orientation = tangentOrToModel (oN p))) :
    IsInducedOrientation j o oN := by
  intro P p hp
  obtain ⟨bb, bb', hsucc, hpos, hor⟩ := hfr p
  rw [P.orientationIn_eq_of_frame o oN hp (hj p) (hgmax p) (hgj p) (hgd p) bb bb' hsucc
    hpos.ne' hor, decide_eq_true hpos]
  cases P.boundarySign o p <;> rfl

/-- **The opposite of the induced orientation from inward frames**: as
`isInducedOrientation_of_outward_frames`, with `dg(w) < 0`; then `−o_N` is the orientation induced
by `j`. -/
theorem isInducedOrientation_neg_of_inward_frames
    (hj : ∀ p, MDifferentiableAt (𝓠 n) (𝓠 (n + 1)) j p) {g : M → ℝ}
    (hgmax : ∀ p, IsLocalMax g (j p)) (hgj : ∀ p, ∀ᶠ q in 𝓝 p, g (j q) = g (j p))
    (hgd : ∀ p, DifferentiableWithinAt ℝ (g ∘ ((chartAt (EuclideanQuadrant (n + 1)) (j p)).extend
      (𝓠 (n + 1))).symm) (range (𝓠 (n + 1)))
      ((chartAt (EuclideanQuadrant (n + 1)) (j p)).extend (𝓠 (n + 1)) (j p)))
    (hfr : ∀ p, ∃ (bb : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
      (bb' : Basis (Fin (n + 1)) ℝ (EuclideanSpace ℝ (Fin (n + 1)))),
      (∀ l, bb' l.succ = mfderiv (𝓠 n) (𝓠 (n + 1)) j p (bb l)) ∧
      derivIn (𝓠 (n + 1)) (chartAt (EuclideanQuadrant (n + 1)) (j p)) g (j p) (bb' 0) < 0 ∧
      (bb'.orientation = tangentOrToModel (o (j p)) ↔
        bb.orientation = tangentOrToModel (oN p))) :
    IsInducedOrientation j o (-oN) := by
  intro P p hp
  obtain ⟨bb, bb', hsucc, hneg, hor⟩ := hfr p
  have h := P.orientationIn_eq_of_frame o oN hp (hj p) (hgmax p) (hgj p) (hgd p) bb bb' hsucc
    hneg.ne hor
  rw [decide_eq_false (not_lt.2 hneg.le)] at h
  have h' : orientationIn P.eN p ((-oN) p) = -orientationIn P.eN p (oN p) := by
    unfold orientationIn
    exact signMap_neg _ _
  rw [h', h]
  cases P.boundarySign o p
  · rfl
  · exact neg_neg _

end FrameCharts

end Polyfold
