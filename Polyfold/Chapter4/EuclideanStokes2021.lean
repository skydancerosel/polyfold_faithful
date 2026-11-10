import Polyfold.Chapter4.EuclideanForms2021
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021): **Stokes' theorem on a
quadrant**, the chart-level case of **Theorem 4.4.7** (p. 199; preprint Theorem 4.28, gap G.40),
of Theorem 6.7.1 and of the branched Stokes theorems of §9.5, with the boundary orientation of
**Definition 9.3.8** (p. 427, outward normal first).  Numbers and pages are the 2021 text's.

# Stokes' theorem on `closedQuadrant S ⊆ ℝⁿ⁺¹`

## The statement

For `S : Finset (Fin (n + 1))`, `Q = closedQuadrant ↑S = {x | 0 ≤ xᵢ for i ∈ S}` and an `n`-form
`ω` on `ℝⁿ⁺¹` that is `C¹` within `Q` and vanishes on `Q` outside a compact set,
`∫_Q dω = ∑_{i ∈ S} ∫_{Fᵢ} ω`, where `Fᵢ = {x ∈ Q | xᵢ = 0}` carries the boundary orientation and
`dω = extDerivWithin ω Q` (Mathlib's exterior derivative, within `Q`).  In the notation of
`EuclideanForms2021.lean` the face integral is
`∫_{Fᵢ} ω = faceSign i * topFormIntegral (closedQuadrant (i.succAbove ⁻¹' ↑S)) (facePullback i ω)`:
the face is parametrized by `faceEmbedding i` (`image_faceEmbedding_quadrant`), and its boundary
orientation is `faceSign i = (-1)^(i+1)` times the orientation of that parametrization
(`det_cons_neg_stdFrame_faceFrame`: `det(-eᵢ, (e_j)_{j ≠ i}) = (-1)^(i+1)` with the outward
vector `-eᵢ` first, as in Definition 9.3.8).

## What is formalized

* `integral_divergence_piQuadrant`: the divergence theorem on a quadrant of `Fin (n + 1) → ℝ` for
  a field vanishing outside a compact set, from Mathlib's divergence theorem on a box
  (`integral_divergence_of_hasFDerivAt_off_countable'`): the box `[a, b]` with `aᵢ = 0` for
  `i ∈ S`, `aᵢ = -R` otherwise and `bᵢ = R` contains the support; its faces `{xᵢ = R}` and
  `{xᵢ = -R}` (`i ∉ S`) miss the support and contribute `0`; the faces `{xᵢ = 0}`, `i ∈ S`, are
  the faces of the quadrant.
* `stokes_quadrant_hyp` (the general form): `ω` continuous on `Q`, differentiable at the points of
  the open quadrant, `dω` integrable on `Q`.
* **`stokes_quadrant`** (`ω` `C¹` within `Q`), `stokes_quadrant_extDeriv` (`ω` `C¹` at the points
  of `Q`, with Mathlib's `extDeriv`), `stokes_quadrant_of_hasCompactSupport`.
* **`stokes_quadrant_inter_open`**: the same on a relatively open subset `U ∩ Q` (`U` open), for
  a form vanishing on `U ∩ Q` outside a compact `K ⊆ U`; the faces are
  `faceEmbedding i ⁻¹' U ∩ closedQuadrant (i.succAbove ⁻¹' ↑S)`.  This is the form the gluing
  along an oriented atlas uses (a chart of a manifold with corners modelled on
  `modelWithCornersEuclideanQuadrant` has target `U ∩ closedQuadrant univ`,
  `range_modelWithCornersEuclideanQuadrant`).

## The corners

Two faces meet only in a corner of codimension `≥ 2`, and the points of the face `Fᵢ` that lie on
other faces form the null set `closedQuadrant \ openQuadrant` of the face parameter space
(`image_faceEmbedding_openQuadrant`, `openQuadrant_ae_eq_quadrant`).  This enters twice: the
boundary `∂Q = ⋃ Fᵢ` is integrated as the sum `∑ᵢ ∫_{Fᵢ}` (no inclusion–exclusion is needed), and
each `∫_{Fᵢ}` may be taken over the points of `Fᵢ` with `d(x) = 1` only, where Definition 9.3.8
defines the boundary orientation (`setIntegral_openQuadrant`).  In the proof it is invisible: the
box faces are closed boxes, and the divergence theorem on a box already integrates over them.
-/

open Set MeasureTheory Filter Topology Module

noncomputable section

namespace Polyfold

/-! ### The divergence theorem on a quadrant of `Fin (n + 1) → ℝ` -/

section PiQuadrant

variable {n : ℕ}

/-- `insertNth i 0 y` lies in the quadrant `S` iff `y` lies in the quadrant `i.succAbove ⁻¹' S`. -/
private theorem insertNth_zero_mem_piQuadrant (S : Finset (Fin (n + 1))) (i : Fin (n + 1))
    (y : Fin n → ℝ) :
    (∀ j ∈ S, (0 : ℝ) ≤ i.insertNth (α := fun _ => ℝ) 0 y j) ↔
      ∀ j, i.succAbove j ∈ S → 0 ≤ y j := by
  constructor
  · intro h j hj
    simpa using h (i.succAbove j) hj
  · intro h j hj
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · simp
    · simpa using h k hj

/-- **The divergence theorem on a quadrant** of `Fin (n + 1) → ℝ`, for a field `f` vanishing on
the quadrant outside a compact set:
`∫_Q ∑ᵢ ∂ᵢ fᵢ = -∑_{i ∈ S} ∫_{y ∈ Qᵢ} fᵢ(insertNth i 0 y) dy`, `Q = {x | 0 ≤ xⱼ, j ∈ S}`,
`Qᵢ = {y | 0 ≤ yⱼ, i.succAbove j ∈ S}`.  The minus sign is the outward normal `-eᵢ`. -/
theorem integral_divergence_piQuadrant (S : Finset (Fin (n + 1)))
    (f : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ)
    (f' : Fin (n + 1) → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℝ)
    {K : Set (Fin (n + 1) → ℝ)} (hK : IsCompact K)
    (hc : ∀ i, ContinuousOn (f i) {x | ∀ j ∈ S, 0 ≤ x j})
    (hd : ∀ x, (∀ j ∈ S, 0 < x j) → ∀ i, HasFDerivAt (f i) (f' i x) x)
    (hi : IntegrableOn (fun x => ∑ i, f' i x (Pi.single i 1)) {x | ∀ j ∈ S, 0 ≤ x j})
    (hf0 : ∀ x, (∀ j ∈ S, 0 ≤ x j) → x ∉ K → ∀ i, f i x = 0)
    (hdiv0 : ∀ x, (∀ j ∈ S, 0 ≤ x j) → x ∉ K → ∑ i, f' i x (Pi.single i 1) = 0) :
    ∫ x in {x | ∀ j ∈ S, 0 ≤ x j}, ∑ i, f' i x (Pi.single i 1) =
      -∑ i ∈ S, ∫ y in {y : Fin n → ℝ | ∀ j, i.succAbove j ∈ S → 0 ≤ y j},
        f i (i.insertNth (α := fun _ => ℝ) 0 y) := by
  classical
  set Q : Set (Fin (n + 1) → ℝ) := {x | ∀ j ∈ S, 0 ≤ x j} with hQ
  -- a bound for the support
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.exists_norm_le
  set R : ℝ := max R₀ 0 + 1 with hR
  have hRpos : 0 < R := by positivity
  have hKR : ∀ x ∈ K, ∀ j, |x j| < R := fun x hx j => by
    have := (norm_le_pi_norm x j).trans (hR₀ x hx)
    rw [Real.norm_eq_abs] at this
    linarith [le_max_left R₀ 0]
  -- the box
  set a : Fin (n + 1) → ℝ := fun j => if j ∈ S then 0 else -R with ha
  set b : Fin (n + 1) → ℝ := fun _ => R with hb
  have hab : a ≤ b := fun j => by
    by_cases hj : j ∈ S <;> simp [a, b, hj, hRpos.le]
  have hboxQ : Icc a b ⊆ Q := fun x hx j hj => by simpa [a, hj] using hx.1 j
  have hKbox : ∀ x ∈ Q, x ∈ K → x ∈ Icc a b := fun x hxQ hxK => by
    refine ⟨fun j => ?_, fun j => (abs_lt.1 (hKR x hxK j)).2.le⟩
    by_cases hj : j ∈ S
    · simpa [a, hj] using hxQ j hj
    · simpa [a, hj] using (abs_lt.1 (hKR x hxK j)).1.le
  have hmeasQ : MeasurableSet Q := by
    simp only [Q, ofPred_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_le measurable_const (measurable_pi_apply j)
  -- reduce the integral over the quadrant to the box
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeasQ hboxQ
    (fun x hx => hdiv0 x hx.1 fun hxK => hx.2 (hKbox x hx.1 hxK))]
  have hHd : ∀ x ∈ (Set.pi univ fun i => Ioo (a i) (b i)) \ (∅ : Set (Fin (n + 1) → ℝ)),
      ∀ i, HasFDerivAt (f i) (f' i x) x := fun x hx i => by
    refine hd x (fun j hj => ?_) i
    simpa [a, hj] using (hx.1 j (mem_univ j)).1
  rw [integral_divergence_of_hasFDerivAt_off_countable' a b hab f f' ∅ countable_empty
    (fun i => (hc i).mono hboxQ) hHd (hi.mono_set hboxQ)]
  -- the faces of the box
  have hfront : ∀ i, ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      f i (i.insertNth (α := fun _ => ℝ) (b i) y) = 0 := fun i =>
    setIntegral_eq_zero_of_forall_eq_zero fun y hy => by
      have hmem : i.insertNth (α := fun _ => ℝ) (b i) y ∈ Icc a b :=
        Fin.insertNth_mem_Icc.2 ⟨⟨hab i, le_rfl⟩, hy⟩
      refine hf0 _ (hboxQ hmem) (fun hK' => ?_) i
      have := hKR _ hK' i
      simp [b, abs_of_pos hRpos] at this
  have hback : ∀ i, ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      f i (i.insertNth (α := fun _ => ℝ) (a i) y) =
        if i ∈ S then ∫ y in {y : Fin n → ℝ | ∀ j, i.succAbove j ∈ S → 0 ≤ y j},
          f i (i.insertNth (α := fun _ => ℝ) 0 y) else 0 := fun i => by
    by_cases hiS : i ∈ S
    · rw [if_pos hiS]
      have hai : a i = 0 := by simp [a, hiS]
      rw [hai]
      have hmeas : MeasurableSet {y : Fin n → ℝ | ∀ j, i.succAbove j ∈ S → 0 ≤ y j} := by
        simp only [ofPred_forall]
        exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
          measurableSet_le measurable_const (measurable_pi_apply j)
      have hsub : Icc (a ∘ i.succAbove) (b ∘ i.succAbove) ⊆
          {y : Fin n → ℝ | ∀ j, i.succAbove j ∈ S → 0 ≤ y j} := fun y hy j hj => by
        simpa [a, hj] using hy.1 j
      refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeas hsub fun y hy => ?_).symm
      have hyQ : i.insertNth (α := fun _ => ℝ) 0 y ∈ Q :=
        (insertNth_zero_mem_piQuadrant S i y).2 hy.1
      refine hf0 _ hyQ (fun hK' => hy.2 ?_) i
      have hbox := hKbox _ hyQ hK'
      rw [Fin.insertNth_mem_Icc] at hbox
      exact hbox.2
    · rw [if_neg hiS]
      refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
      have hmem : i.insertNth (α := fun _ => ℝ) (a i) y ∈ Icc a b :=
        Fin.insertNth_mem_Icc.2 ⟨⟨le_rfl, hab i⟩, hy⟩
      refine hf0 _ (hboxQ hmem) (fun hK' => ?_) i
      have := hKR _ hK' i
      simp [a, hiS, abs_of_pos hRpos] at this
  simp only [hfront, hback, zero_sub, Finset.sum_neg_distrib]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

end PiQuadrant

/-! ### Stokes' theorem on a quadrant of `ℝⁿ⁺¹` -/

section Stokes

variable {n : ℕ}

/-- A form vanishing near `x` within `s` has exterior derivative `0` at `x` within `s`. -/
theorem extDerivWithin_eq_zero_of_eventuallyEq_zero {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
    {ω : E → E [⋀^Fin k]→L[ℝ] F} {s : Set E} {x : E} (h : ω =ᶠ[𝓝[s] x] 0) (hx : ω x = 0) :
    extDerivWithin ω s x = 0 := by
  rw [extDerivWithin, h.fderivWithin_eq hx, fderivWithin_zero]
  exact map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F)

/-- A form vanishing on `s \ K`, `K` closed, has exterior derivative `0` on `s \ K`. -/
theorem extDerivWithin_eq_zero_of_notMem {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
    {ω : E → E [⋀^Fin k]→L[ℝ] F} {s K : Set E} (hK : IsClosed K)
    (hωK : ∀ y ∈ s, y ∉ K → ω y = 0) {x : E} (hxs : x ∈ s) (hxK : x ∉ K) :
    extDerivWithin ω s x = 0 := by
  refine extDerivWithin_eq_zero_of_eventuallyEq_zero ?_ (hωK x hxs hxK)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hK.isOpen_compl.mem_nhds hxK)]
    with y hys hyK
  exact hωK y hys hyK

/-- **Stokes' theorem on a quadrant, general hypotheses** (the chart-level case of Theorem 4.4.7,
2021 p. 199; preprint Theorem 4.28): for an `n`-form `ω` on `ℝⁿ⁺¹` vanishing on
`Q = closedQuadrant ↑S` outside a compact set, continuous on `Q`, differentiable at the points of
the open quadrant, with `dω = extDerivWithin ω Q` integrable on `Q`,
`∫_Q dω = ∑_{i ∈ S} faceSign i * ∫_{closedQuadrant (i.succAbove ⁻¹' S)} ιᵢ^*ω`, the faces with the
boundary orientation (outward normal first, Definition 9.3.8). -/
theorem stokes_quadrant_hyp (S : Finset (Fin (n + 1)))
    {ω : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) [⋀^Fin n]→L[ℝ] ℝ}
    {K : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hK : IsCompact K)
    (hωK : ∀ x ∈ closedQuadrant (S : Set (Fin (n + 1))), x ∉ K → ω x = 0)
    (hc : ContinuousOn ω (closedQuadrant (S : Set (Fin (n + 1)))))
    (hd : ∀ x ∈ openQuadrant (S : Set (Fin (n + 1))), DifferentiableAt ℝ ω x)
    (hi : IntegrableOn (fun x => extDerivWithin ω (closedQuadrant (S : Set (Fin (n + 1)))) x
      (stdFrame (n + 1))) (closedQuadrant (S : Set (Fin (n + 1))))) :
    topFormIntegral (closedQuadrant (S : Set (Fin (n + 1))))
        (extDerivWithin ω (closedQuadrant (S : Set (Fin (n + 1))))) =
      ∑ i ∈ S, faceSign i *
        topFormIntegral (closedQuadrant (i.succAbove ⁻¹' (S : Set (Fin (n + 1)))))
          (facePullback i ω) := by
  classical
  set Q := closedQuadrant (S : Set (Fin (n + 1))) with hQ
  set e := stdFrame (n + 1) with he
  let T : (Fin (n + 1) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => ℝ)).symm.toContinuousLinearMap
  have hT : ⇑T = WithLp.toLp 2 := PiLp.coe_symm_continuousLinearEquiv 2 ℝ _
  let D : EuclideanSpace ℝ (Fin (n + 1)) → _ := fun y => fderivWithin ℝ ω Q y
  let f : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ := fun i x =>
    (-1 : ℝ) ^ (i : ℕ) * ω (WithLp.toLp 2 x) (i.removeNth e)
  let f' : Fin (n + 1) → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℝ := fun i x =>
    (-1 : ℝ) ^ (i : ℕ) •
      ((ContinuousAlternatingMap.apply ℝ _ ℝ (i.removeNth e)).comp ((D (WithLp.toLp 2 x)).comp T))
  -- the divergence of `f` is `dω`
  have hdiv : ∀ x, ∑ i, f' i x (Pi.single i 1) = extDerivWithin ω Q (WithLp.toLp 2 x) e :=
    fun x => by
      rw [extDerivWithin, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [f', D, hT, he, stdFrame_eq_toLp_single]
  have hQpi : WithLp.toLp 2 ⁻¹' Q = {x : Fin (n + 1) → ℝ | ∀ j ∈ S, 0 ≤ x j} := by
    ext x; simp [Q, closedQuadrant]
  have hface : ∀ i : Fin (n + 1), WithLp.toLp 2 ⁻¹' closedQuadrant (i.succAbove ⁻¹' (S : Set _)) =
      {y : Fin n → ℝ | ∀ j, i.succAbove j ∈ S → 0 ≤ y j} := fun i => by
    ext; simp [closedQuadrant]
  have hmp := PiLp.volume_preserving_toLp (Fin (n + 1))
  have hme : MeasurableEmbedding (WithLp.toLp 2 : (Fin (n + 1) → ℝ) → _) := by
    have := (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).measurableEmbedding
    rwa [MeasurableEquiv.coe_toLp] at this
  have hmp' := PiLp.volume_preserving_toLp (Fin n)
  have hme' : MeasurableEmbedding (WithLp.toLp 2 : (Fin n → ℝ) → _) := by
    have := (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
    rwa [MeasurableEquiv.coe_toLp] at this
  have hmeasQpi : MeasurableSet {x : Fin (n + 1) → ℝ | ∀ j ∈ S, 0 ≤ x j} :=
    hQpi ▸ measurableSet_quadrant.preimage hme.measurable
  have key := integral_divergence_piQuadrant S f f' (K := WithLp.ofLp '' K)
    (hK.image (PiLp.continuous_ofLp 2 _)) ?hc ?hd ?hi ?hf0 ?hdiv0
  case hc =>
    intro i
    rw [← hQpi]
    exact continuousOn_const.mul
      ((ContinuousAlternatingMap.apply ℝ _ ℝ (i.removeNth e)).continuous.comp_continuousOn
        (hc.comp (PiLp.continuous_toLp 2 _).continuousOn (mapsTo_preimage _ _)))
  case hd =>
    intro x hx i
    have hy : WithLp.toLp 2 x ∈ openQuadrant (S : Set (Fin (n + 1))) := fun j hj => by
      simpa using hx j hj
    have h1 : HasFDerivAt ω (D (WithLp.toLp 2 x)) (WithLp.toLp 2 x) := by
      have := (hd _ hy).hasFDerivAt
      rwa [← fderivWithin_of_mem_nhds (quadrant_mem_nhds hy)] at this
    have hT' : HasFDerivAt (WithLp.toLp 2) T x := hT ▸ T.hasFDerivAt
    have h2 := ((ContinuousAlternatingMap.apply ℝ _ ℝ (i.removeNth e)).hasFDerivAt).comp x
      (h1.comp x hT')
    exact h2.const_mul _
  case hi =>
    have : (fun x => ∑ i, f' i x (Pi.single i 1)) =
        (fun y => extDerivWithin ω Q y e) ∘ WithLp.toLp 2 := funext hdiv
    rw [this, ← hQpi]
    exact (hmp.integrableOn_comp_preimage hme).2 hi
  case hf0 =>
    intro x hx hxK i
    have : ω (WithLp.toLp 2 x) = 0 :=
      hωK _ (by simpa [hQ, closedQuadrant] using hx) fun h => hxK ⟨_, h, rfl⟩
    simp [f, this]
  case hdiv0 =>
    intro x hx hxK
    rw [hdiv]
    rw [extDerivWithin_eq_zero_of_notMem hK.isClosed hωK (by simpa [hQ, closedQuadrant] using hx)
      fun h => hxK ⟨_, h, rfl⟩]
    simp
  -- transport both sides
  have hL : topFormIntegral Q (extDerivWithin ω Q) =
      ∫ x in {x : Fin (n + 1) → ℝ | ∀ j ∈ S, 0 ≤ x j}, ∑ i, f' i x (Pi.single i 1) := by
    rw [topFormIntegral, ← hmp.setIntegral_preimage_emb hme, hQpi]
    exact setIntegral_congr_fun hmeasQpi fun x _ => (hdiv x).symm
  have hR : ∀ i : Fin (n + 1),
      topFormIntegral (closedQuadrant (i.succAbove ⁻¹' (S : Set _))) (facePullback i ω) =
        ∫ y in {y : Fin n → ℝ | ∀ j, i.succAbove j ∈ S → 0 ≤ y j},
          ω (WithLp.toLp 2 (i.insertNth (α := fun _ => ℝ) 0 y)) (i.removeNth e) := fun i => by
    rw [topFormIntegral, ← hmp'.setIntegral_preimage_emb hme', hface]
    simp only [facePullback_stdFrame, faceEmbedding_apply, he]
  rw [hL, key]
  simp only [hR, f, integral_const_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [faceSign, pow_succ]
  ring

/-- The exterior derivative within `s` of a `C¹` form is continuous on `s` (for unique
differentiability on `s`), evaluated on fixed vectors. -/
theorem continuousOn_extDerivWithin_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} {ω : E → E [⋀^Fin k]→L[ℝ] F} {s : Set E}
    (hω : ContDiffOn ℝ 1 ω s) (hs : UniqueDiffOn ℝ s) (v : Fin (k + 1) → E) :
    ContinuousOn (fun x => extDerivWithin ω s x v) s :=
  ((ContinuousAlternatingMap.apply ℝ _ F v).continuous.comp
    (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F).continuous).comp_continuousOn
      (hω.continuousOn_fderivWithin hs le_rfl)

/-- `extDerivWithin` only sees the germ of the set: `d` within `s ∩ t` equals `d` within `s` at a
point of which `t` is a neighbourhood. -/
theorem extDerivWithin_inter_of_mem_nhds {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} (ω : E → E [⋀^Fin k]→L[ℝ] F) {s t : Set E}
    {x : E} (ht : t ∈ 𝓝 x) : extDerivWithin ω (s ∩ t) x = extDerivWithin ω s x := by
  simp only [extDerivWithin, fderivWithin_inter ht]

/-- **Stokes' theorem on a quadrant** (the chart-level case of Theorem 4.4.7, 2021 p. 199;
preprint Theorem 4.28).  For an `n`-form `ω` on `ℝⁿ⁺¹`, `C¹` within `Q = closedQuadrant ↑S` and
vanishing on `Q` outside a compact set `K`,
`∫_Q dω = ∑_{i ∈ S} ∫_{Fᵢ} ω`, `dω = extDerivWithin ω Q`, where the face `Fᵢ = {xᵢ = 0}` carries
the boundary orientation of Definition 9.3.8 (outward normal first):
`∫_{Fᵢ} ω = faceSign i * ∫_{closedQuadrant (i.succAbove ⁻¹' S)} ιᵢ^*ω`. -/
theorem stokes_quadrant (S : Finset (Fin (n + 1)))
    {ω : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) [⋀^Fin n]→L[ℝ] ℝ}
    {K : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hK : IsCompact K)
    (hωK : ∀ x ∈ closedQuadrant (S : Set (Fin (n + 1))), x ∉ K → ω x = 0)
    (hω : ContDiffOn ℝ 1 ω (closedQuadrant (S : Set (Fin (n + 1))))) :
    topFormIntegral (closedQuadrant (S : Set (Fin (n + 1))))
        (extDerivWithin ω (closedQuadrant (S : Set (Fin (n + 1))))) =
      ∑ i ∈ S, faceSign i *
        topFormIntegral (closedQuadrant (i.succAbove ⁻¹' (S : Set (Fin (n + 1)))))
          (facePullback i ω) := by
  refine stokes_quadrant_hyp S hK hωK hω.continuousOn (fun x hx =>
    ((hω.differentiableOn one_ne_zero) x (openQuadrant_subset_quadrant hx)).differentiableAt
      (quadrant_mem_nhds hx)) ?_
  have hcont := continuousOn_extDerivWithin_apply hω uniqueDiffOn_quadrant (stdFrame (n + 1))
  refine IntegrableOn.of_forall_sdiff_eq_zero ((hcont.mono inter_subset_left).integrableOn_compact
    (hK.inter_left isClosed_quadrant)) measurableSet_quadrant fun x hx => ?_
  rw [extDerivWithin_eq_zero_of_notMem hK.isClosed hωK hx.1 fun h => hx.2 ⟨hx.1, h⟩]
  rfl

/-- **Stokes' theorem on a quadrant, for a form `C¹` near `Q`**, with Mathlib's `extDeriv`: if `ω`
is `C¹` at every point of `Q = closedQuadrant ↑S` (e.g. `C¹` on an open neighbourhood of `Q`) and
vanishes on `Q` outside a compact set, `∫_Q dω = ∑_{i ∈ S} ∫_{Fᵢ} ω`. -/
theorem stokes_quadrant_extDeriv (S : Finset (Fin (n + 1)))
    {ω : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) [⋀^Fin n]→L[ℝ] ℝ}
    {K : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hK : IsCompact K)
    (hωK : ∀ x ∈ closedQuadrant (S : Set (Fin (n + 1))), x ∉ K → ω x = 0)
    (hω : ∀ x ∈ closedQuadrant (S : Set (Fin (n + 1))), ContDiffAt ℝ 1 ω x) :
    topFormIntegral (closedQuadrant (S : Set (Fin (n + 1)))) (extDeriv ω) =
      ∑ i ∈ S, faceSign i *
        topFormIntegral (closedQuadrant (i.succAbove ⁻¹' (S : Set (Fin (n + 1)))))
          (facePullback i ω) := by
  rw [← stokes_quadrant S hK hωK fun x hx => (hω x hx).contDiffWithinAt]
  refine topFormIntegral_congr measurableSet_quadrant fun x hx => ?_
  rw [extDerivWithin, extDeriv, fderivWithin_eq_fderiv (uniqueDiffOn_quadrant x hx)
    ((hω x hx).differentiableAt one_ne_zero)]

/-- **Stokes' theorem on a quadrant for a compactly supported form.** -/
theorem stokes_quadrant_of_hasCompactSupport (S : Finset (Fin (n + 1)))
    {ω : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) [⋀^Fin n]→L[ℝ] ℝ}
    (hsupp : HasCompactSupport ω) (hω : ContDiffOn ℝ 1 ω (closedQuadrant (S : Set (Fin (n + 1))))) :
    topFormIntegral (closedQuadrant (S : Set (Fin (n + 1))))
        (extDerivWithin ω (closedQuadrant (S : Set (Fin (n + 1))))) =
      ∑ i ∈ S, faceSign i *
        topFormIntegral (closedQuadrant (i.succAbove ⁻¹' (S : Set (Fin (n + 1)))))
          (facePullback i ω) :=
  stokes_quadrant S hsupp.isCompact (fun _ _ hx => image_eq_zero_of_notMem_tsupport hx) hω

/-- **Stokes' theorem on a relatively open subset of a quadrant** (the form used by the gluing
along an atlas: a chart of a manifold with corners modelled on the quadrant has target `U ∩ Q`).
For `U` open, an `n`-form `ω` `C¹` within `U ∩ Q`, `Q = closedQuadrant ↑S`, and vanishing on `U ∩ Q`
outside a compact `K ⊆ U`:
`∫_{U ∩ Q} dω = ∑_{i ∈ S} faceSign i * ∫_{ιᵢ⁻¹(U) ∩ closedQuadrant (i.succAbove ⁻¹' S)} ιᵢ^*ω`,
`dω = extDerivWithin ω (U ∩ Q)`, the faces with the boundary orientation of Definition 9.3.8. -/
theorem stokes_quadrant_inter_open (S : Finset (Fin (n + 1)))
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hU : IsOpen U)
    {ω : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) [⋀^Fin n]→L[ℝ] ℝ}
    {K : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hK : IsCompact K) (hKU : K ⊆ U)
    (hωK : ∀ x ∈ U ∩ closedQuadrant (S : Set (Fin (n + 1))), x ∉ K → ω x = 0)
    (hω : ContDiffOn ℝ 1 ω (U ∩ closedQuadrant (S : Set (Fin (n + 1))))) :
    topFormIntegral (U ∩ closedQuadrant (S : Set (Fin (n + 1))))
        (extDerivWithin ω (U ∩ closedQuadrant (S : Set (Fin (n + 1))))) =
      ∑ i ∈ S, faceSign i *
        topFormIntegral
          (faceEmbedding i ⁻¹' U ∩ closedQuadrant (i.succAbove ⁻¹' (S : Set (Fin (n + 1)))))
          (facePullback i ω) := by
  classical
  set Q := closedQuadrant (S : Set (Fin (n + 1))) with hQ
  -- extend `ω` by `0` off `U`
  set ω' : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) [⋀^Fin n]→L[ℝ] ℝ :=
    U.piecewise ω 0 with hω'
  have hω'U : EqOn ω' ω U := fun x hx => U.piecewise_eq_of_mem _ _ hx
  have hω'K : ∀ x ∈ Q, x ∉ K → ω' x = 0 := fun x hxQ hxK => by
    by_cases hxU : x ∈ U
    · rw [hω'U hxU]; exact hωK x ⟨hxU, hxQ⟩ hxK
    · exact U.piecewise_eq_of_notMem _ _ hxU
  have hloc0 : ∀ x ∉ K, ω' =ᶠ[𝓝[Q] x] 0 := fun x hxK => by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (hK.isClosed.isOpen_compl.mem_nhds hxK)] with y hyQ hyK
    exact hω'K y hyQ hyK
  have hω'C : ContDiffOn ℝ 1 ω' Q := fun x hxQ => by
    by_cases hxU : x ∈ U
    · have h1 : ContDiffWithinAt ℝ 1 ω Q x := by
        have := hω x ⟨hxU, hxQ⟩
        rw [inter_comm] at this
        exact (contDiffWithinAt_inter (hU.mem_nhds hxU)).1 this
      exact h1.congr_of_eventuallyEq
        (nhdsWithin_le_nhds (eventuallyEq_of_mem (hU.mem_nhds hxU) hω'U)) (hω'U hxU)
    · have hxK : x ∉ K := fun h => hxU (hKU h)
      exact contDiffWithinAt_const.congr_of_eventuallyEq (hloc0 x hxK) (hω'K x hxQ hxK)
  have main := stokes_quadrant S hK hω'K hω'C
  -- the left side
  have hL : topFormIntegral (U ∩ Q) (extDerivWithin ω (U ∩ Q)) =
      topFormIntegral Q (extDerivWithin ω' Q) := by
    rw [topFormIntegral_eq_of_subset measurableSet_quadrant inter_subset_right fun x hx =>
      extDerivWithin_eq_zero_of_eventuallyEq_zero (hloc0 x fun h => hx.2 ⟨hKU h, hx.1⟩)
        (hω'K x hx.1 fun h => hx.2 ⟨hKU h, hx.1⟩)]
    refine topFormIntegral_congr (hU.measurableSet.inter measurableSet_quadrant) fun x hx => ?_
    rw [extDerivWithin_congr' (hω'U.mono inter_subset_left).symm hx, inter_comm,
      extDerivWithin_inter_of_mem_nhds ω' (hU.mem_nhds hx.1)]
  -- the faces
  have hR : ∀ i : Fin (n + 1),
      topFormIntegral
          (faceEmbedding i ⁻¹' U ∩ closedQuadrant (i.succAbove ⁻¹' (S : Set (Fin (n + 1)))))
          (facePullback i ω) =
        topFormIntegral (closedQuadrant (i.succAbove ⁻¹' (S : Set (Fin (n + 1)))))
          (facePullback i ω') :=
    fun i => by
      rw [topFormIntegral_eq_of_subset measurableSet_quadrant inter_subset_right fun y hy => ?_]
      · refine topFormIntegral_congr ((hU.measurableSet.preimage
          (faceEmbedding i).continuous.measurable).inter measurableSet_quadrant) fun y hy => ?_
        simp [facePullback, formPullback, hω'U hy.1]
      · have hyU : faceEmbedding i y ∉ U := fun h => hy.2 ⟨h, hy.1⟩
        have h0 : ω' (faceEmbedding i y) = 0 := U.piecewise_eq_of_notMem _ _ hyU
        ext v
        simp [facePullback, formPullback, h0]
  rw [hL, main]
  exact Finset.sum_congr rfl fun i _ => by rw [hR i]

end Stokes

end Polyfold
