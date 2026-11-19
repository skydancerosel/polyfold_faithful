import Polyfold.Chapter9.CyclicGroupoidIsotropy
import Polyfold.Chapter9.HalfCircleSheet

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, §9.5,
**Remark 9.5.20** (pp. 451–452; 2017: Remark 9.8), point G.110: the submanifold
`M = [−1, 1] × {0}` of the M-polyfold `X` of `DimensionJumpPolyfold.lean`.

# `M = [−1, 1] × {0}` is a tame `1`-dimensional submanifold of `X`

## The text, paraphrased
(p. 451) `M = [−1,1] × {0}` is a smooth submanifold of `X`, oriented by the standard orientation
of `[−1, 1]`.

## What is formalized
In the namespace `Polyfold.DimensionJump`.
* `sM (t, z) = (t, 0)`: in the chart of `X` it is the sc-operator `(p, a, b) ↦ (p, 0, 0)`, an
  sc⁺-operator (it maps `E_m` into `E_{m+1}`), so `sM` is an sc⁺-retraction of `X`
  (`sM_isScPlusRetractionOn`, Definition 4.1.4) with image `M` (`isSmoothSubmanifold_M`,
  Definition 4.2.1).
* The chart model of `M` is the quarter circle `arc × {0}`, the retract of
  `RM (p, a, b) = (ρ p, 0, 0)`; at `(p, 0, 0)` the derivative of `RM` is the orthogonal
  projection onto `p^⊥ × {0}` (`scDeriv_RM`), so `T_yM` is a line
  (`isSubmanifoldOfDim_M`, Remark 9.1.1).
* `RM` is a tame retraction (Definition 2.5.2): `ρ` keeps the vanishing coordinates, and
  `ℝp ⊕ (X_w ⊕ X_w)` is an sc-complement of `p^⊥ × {0}` lying in `E_x`, also at the two end
  points.  Hence the structure induced on `M` is tame (`hasTameInducedStructure_M`, 2021
  Definition 2.5.18), including at the points `(±1, 0)` where `X` is infinite-dimensional.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology Module Submodule
open scoped ContDiff Real

noncomputable section

namespace Polyfold

namespace DimensionJump

open DimensionJump
open ScOneExample hiding E

open RemarkFourThree MPolyfold

/-! ### The sc⁺-retraction `(t, z) ↦ (t, 0)` -/

lemma mk_zero_mem {x : XR} : (x.1.1, (0 : ℂ)) ∈ Xs := by
  rcases mem_Xs_iff.1 x.2 with h | h | h
  · rw [h]; exact mem_Xs_iff.2 (Or.inl rfl)
  · rw [h]; exact mem_Xs_iff.2 (Or.inr (Or.inl rfl))
  · exact mem_Xs_iff.2 (Or.inr (Or.inr ⟨h.1, by simp⟩))

/-- **`sM (t, z) = (t, 0)`**, the retraction of `X` onto `M = [−1,1] × {0}`. -/
def sM (x : XR) : XR := ⟨(x.1.1, 0), mk_zero_mem⟩

lemma sM_val (x : XR) : (sM x : ℝ × ℂ) = (x.1.1, 0) := rfl

/-- **The submanifold `M = [−1,1] × {0}`** of `X`. -/
def Mset : Set XR := {x | x.1.2 = 0}

lemma sM_mem (x : XR) : sM x ∈ Mset := rfl

lemma sM_eq_self {x : XR} (hx : x ∈ Mset) : sM x = x :=
  Subtype.ext (Prod.ext rfl (show (0 : ℂ) = x.1.2 from hx.symm))

lemma sM_image : sM '' univ = Mset ∩ univ := by
  rw [inter_univ]
  exact Subset.antisymm (image_subset_iff.2 fun x _ => sM_mem x)
    fun x hx => ⟨x, mem_univ _, sM_eq_self hx⟩

/-- The zero operator of `X_w ⊕ X_w`. -/
def zeroZ : ScOperator Z2 Z2 where
  lvl _ := 0
  incl_comm m _ := map_zero (Z2.incl m)

/-- The projection `(p, a, b) ↦ (p, 0, 0)` of `E = ℝ² ⊕ (X_w ⊕ X_w)`. -/
def prM : ScOperator E E := ScOperator.prodMap (ScOperator.id _) zeroZ

lemma prM_apply (q : E 0) : prM 0 q = ((q.1, 0) : E 0) := rfl

/-- The same projection as an sc⁺-operator `E → E¹`. -/
def prMPlus : ScOperator E E.shift where
  lvl m := ContinuousLinearMap.prodMap (ContinuousLinearMap.id ℝ V2) (0 : Z2 m →L[ℝ] Z2 (m + 1))
  incl_comm m _ := Prod.ext rfl (by
    change Z2.incl (m + 1) 0 = 0
    exact map_zero _)

lemma toBase_prMPlus (q : E 0) : E.toBase 1 (prMPlus 0 q) = ((q.1, 0) : E 0) := by
  rw [ScBanach.prod_toBase, ScBanach.const_toBase]
  change ((q.1, Z2.toBase 1 0) : E 0) = _
  rw [map_zero]

lemma liftOne_prM (q : E 0) : E.liftOne (prM 0 q) = prMPlus 0 q :=
  (E.liftOne_eq_iff ⟨prMPlus 0 q, toBase_prMPlus q⟩).2 (toBase_prMPlus q)

lemma chart_sM (x : XR) : chart (sM x) = prM 0 (chart x) := by
  rw [chart_apply, chart_apply, prM_apply]
  simp only [ψfun, sM_val, wdisk_zero, Complex.zero_re, Complex.zero_im, zero_smul]
  rfl

lemma himg_chart : chart.toPartialEquiv '' univ = O := chart.toPartialEquiv.image_source_eq_target

lemma prM_mapsTo : MapsTo (prM 0) O O := by
  intro q hq
  obtain ⟨x, -, rfl⟩ := himg_chart.symm ▸ hq
  rw [← chart_sM]
  exact ψfun_mem_O (sM x).2

/-- **`sM` is sc-smooth**: in the chart it is the sc-operator `prM`. -/
theorem isScSmoothMap_sM : P.IsScSmoothMap P sM := by
  refine IsScSmoothOn.of_exists_charts isOpen_univ ?_ fun y _ => ⟨chart, chart, univ,
    isChart_chart, isChart_chart, isOpen_univ, mem_univ _, fun z _ => ⟨mem_univ _, mem_univ _⟩,
    fun z _ => mem_univ _, ?_⟩
  · exact (Continuous.subtype_mk ((continuous_subtype_val.fst).prodMk continuous_const)
      _).continuousOn
  · have key : IsScSmoothRetractMap E (quadrant 2 Z2 0) O E (quadrant 2 Z2 0) O (prM 0) :=
      prM.isScSmoothRetractMap Rt.isScRetract prM_mapsTo
    rw [himg_chart]
    refine key.congr fun q hq => ?_
    obtain ⟨x, -, rfl⟩ := himg_chart.symm ▸ hq
    change prM 0 (chart x) = chart (sM (chart.symm (chart x)))
    rw [chart.symm_apply_apply (mem_univ x)]
    exact (chart_sM x).symm

lemma mem_smoothSet_sM (x : XR) : sM x ∈ P.smoothSet := mem_smoothSet_of_snd_eq_zero rfl

/-- **`sM` is an sc⁺-retraction of `X`** (Definition 4.1.4): in the chart, `1₀¹ ∘ sM` is the
sc⁺-operator `prMPlus : E → E¹`. -/
theorem sM_isScPlusRetractionOn : P.IsScPlusRetractionOn sM univ where
  isScSmoothOn := isScSmoothMap_sM
  mapsTo _ _ := mem_univ _
  idem x _ := sM_eq_self (sM_mem x)
  mem_levelSet x _ := P.smoothSet_subset_levelSet 1 (mem_smoothSet_sM x)
  isScSmoothOn_one x₀ := by
    refine IsScSmoothOn.of_exists_charts isOpen_univ ?_ fun y _ => ⟨chart,
      levelChart isChart_chart x₀, univ, isChart_chart, P.shift_isChart isChart_chart x₀,
      isOpen_univ, mem_univ _, fun z _ => ⟨mem_univ _, mem_univ _⟩, fun z _ => mem_univ _, ?_⟩
    · -- continuity: read in the chart of `X¹`
      have hc : ContinuousOn (levelChart isChart_chart x₀).symm
          (levelChart isChart_chart x₀).toPartialEquiv.target :=
        (levelChart isChart_chart x₀).continuousOn_invFun
      have hmaps : MapsTo (fun x : XR => prMPlus 0 (chart x)) univ
          (levelChart isChart_chart x₀).toPartialEquiv.target := by
        intro x _
        have e : E.toBase 1 (prMPlus 0 (chart x)) = chart (sM x) :=
          (toBase_prMPlus _).trans (chart_sM x).symm
        change E.toBase 1 (prMPlus 0 (chart x)) ∈ O
        rw [e]
        exact ψfun_mem_O (sM x).2
      have h1 : ContinuousOn (fun x : XR => (levelChart isChart_chart x₀).symm
          (prMPlus 0 (chart x))) univ :=
        hc.comp ((prMPlus 0).continuous.comp_continuousOn chart.continuousOn_toFun) hmaps
      refine h1.congr fun x _ => ?_
      simp only [Function.comp_apply]
      have hx1 : sM x ∈ P.levelSet 1 := P.smoothSet_subset_levelSet 1 (mem_smoothSet_sM x)
      have hsrc : P.toLevelOne x₀ (sM x) ∈ (levelChart isChart_chart x₀).source := by
        change P.levelVal 1 (P.toLevelOne x₀ (sM x)) ∈ chart.source
        exact mem_univ _
      rw [← (levelChart isChart_chart x₀).symm_apply_apply hsrc,
        levelChart_toLevelOne isChart_chart x₀ x₀ hx1, chart_sM]
      exact congrArg _ (liftOne_prM _)
    · have hmaps : MapsTo (prMPlus 0) O (E.lvlSet O 1) := by
        intro q hq
        rw [ScBanach.mem_lvlSet, toBase_prMPlus, ← prM_apply]
        exact prM_mapsTo hq
      have key : IsScSmoothRetractMap E (quadrant 2 Z2 0) O E.shift (E.lvlSet (quadrant 2 Z2 0) 1)
          (E.lvlSet O 1) (prMPlus 0) :=
        prMPlus.isScSmoothRetractMap Rt.isScRetract hmaps
      rw [himg_chart]
      refine key.congr fun q hq => ?_
      obtain ⟨x, -, rfl⟩ := himg_chart.symm ▸ hq
      change prMPlus 0 (chart x) =
        levelChart isChart_chart x₀ (P.toLevelOne x₀ (sM (chart.symm (chart x))))
      rw [chart.symm_apply_apply (mem_univ x), levelChart_toLevelOne isChart_chart x₀ x₀
        (P.smoothSet_subset_levelSet 1 (mem_smoothSet_sM x)), chart_sM]
      exact (liftOne_prM _).symm

/-- **`M = [−1,1] × {0}` is a smooth finite-dimensional submanifold of `X`** (Definition 4.2.1,
Remark 9.5.20, p. 451): the image of the sc⁺-retraction `sM`. -/
theorem isSmoothSubmanifold_M : P.IsSmoothSubmanifold Mset := fun _ _ =>
  ⟨univ, isOpen_univ, mem_univ _, sM, sM_isScPlusRetractionOn, sM_image⟩

/-- The data `(X, sM)` of `M` (Definition 4.2.1). -/
def mData : P.SubmanifoldData Mset := ⟨univ, sM, isOpen_univ, sM_isScPlusRetractionOn, sM_image⟩

/-! ### The tangent spaces of `M` -/

/-- `h ↦ ⟨p, h⟩`. -/
def ellP (p : V2) : V2 →L[ℝ] ℝ :=
  p 0 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 +
    p 1 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1

@[simp] lemma ellP_apply (p h : V2) : ellP p h = p 0 * h 0 + p 1 * h 1 := by
  simp [ellP]

/-- The derivative of `ρ` on the quarter circle: `h ↦ h − ⟨p, h⟩ p / 4`. -/
def dρ (p : V2) : V2 →L[ℝ] V2 := ContinuousLinearMap.id ℝ V2 - (1 / 4 : ℝ) • (ellP p).smulRight p

lemma dρ_apply (p h : V2) : dρ p h = h - ((1 / 4 : ℝ) * ellP p h) • p := by
  simp [dρ, smul_smul]

lemma sq_add_sq_of_mem_arc {p : V2} (hp : p ∈ arc) : p 0 ^ 2 + p 1 ^ 2 = 4 := by
  have h2 := hp.2
  rw [len] at h2
  have := Real.sq_sqrt (show 0 ≤ p 0 ^ 2 + p 1 ^ 2 by positivity)
  rw [h2] at this
  linarith

lemma hasFDerivAt_ρ {p : V2} (hp : p ∈ arc) : HasFDerivAt ρ (dρ p) p := by
  have hs : HasFDerivAt (fun q : V2 => q 0 ^ 2 + q 1 ^ 2) ((2 : ℝ) • ellP p) p := by
    have h := (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).hasFDerivAt
      (x := p)).pow 2).add
      (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).hasFDerivAt (x := p)).pow 2)
    refine h.congr_fderiv (ContinuousLinearMap.ext fun h => ?_)
    simp; ring
  have h4 := sq_add_sq_of_mem_arc hp
  have hlen : len p = 2 := hp.2
  have hl : HasFDerivAt len ((1 / (2 * 2) : ℝ) • (2 : ℝ) • ellP p) p := by
    have := HasFDerivAt.sqrt hs (by rw [h4]; norm_num)
    rw [show √(p 0 ^ 2 + p 1 ^ 2) = 2 from hlen] at this
    exact this
  have hi := (hasDerivAt_inv (show len p ≠ 0 by rw [hlen]; norm_num)).comp_hasFDerivAt p hl
  have hc := HasFDerivAt.smul (HasFDerivAt.const_mul hi (2 : ℝ)) (hasFDerivAt_id p)
  have e : ((fun y => 2 * ((fun y : ℝ => y⁻¹) ∘ len) y) • (id : V2 → V2)) = ρ := by
    funext y; simp [ρ, div_eq_mul_inv]
  rw [e] at hc
  refine hc.congr_fderiv (ContinuousLinearMap.ext fun h => ?_)
  rw [dρ_apply]
  ext i
  simp [ellP_apply, hlen]
  ring


lemma ellP_self {p : V2} (hp : p ∈ arc) : ellP p p = 4 := by
  rw [ellP_apply, ← sq_add_sq_of_mem_arc hp]; ring

lemma dρ_idem {p : V2} (hp : p ∈ arc) (h : V2) : dρ p (dρ p h) = dρ p h := by
  have e : ellP p (dρ p h) = 0 := by
    rw [dρ_apply, map_sub, map_smul, ellP_self hp, smul_eq_mul]; ring
  conv_lhs => rw [dρ_apply, e, mul_zero, zero_smul, sub_zero]

/-- The rotated vector `J p = (−p₁, p₀)`, tangent to the circle at `p`. -/
def Jp (p : V2) : V2 := ![-(p 1), p 0]

lemma ellP_Jp (p : V2) : ellP p (Jp p) = 0 := by
  simp [ellP_apply, Jp]; ring

lemma dρ_Jp (p : V2) : dρ p (Jp p) = Jp p := by
  rw [dρ_apply, ellP_Jp, mul_zero, zero_smul, sub_zero]

lemma dρ_eq_smul_Jp {p : V2} (hp : p ∈ arc) (h : V2) :
    dρ p h = ((1 / 4 : ℝ) * (-(p 1) * h 0 + p 0 * h 1)) • Jp p := by
  have h4 := sq_add_sq_of_mem_arc hp
  rw [dρ_apply]
  ext i
  fin_cases i <;> simp [Jp, ellP_apply] <;> linear_combination (-(1 / 4 : ℝ) * h _) * h4

lemma Jp_ne_zero {p : V2} (hp : p ∈ arc) : Jp p ≠ 0 := by
  intro h
  have h0 : p 1 = 0 := by have := congrFun h 0; simpa [Jp] using this
  have h1 : p 0 = 0 := by have := congrFun h 1; simpa [Jp] using this
  exact ne_zero_of_mem_arc hp (funext fun i => by fin_cases i <;> assumption)

lemma eq_smul_of_dρ_eq_zero {p v : V2} (hv : dρ p v = 0) : v = ((1 / 4 : ℝ) * ellP p v) • p := by
  rw [dρ_apply, sub_eq_zero] at hv; exact hv

/-- The derivative of `RM` at `(p, 0, 0)`: `(h, a, b) ↦ (h − ⟨p, h⟩p/4, 0, 0)`, an idempotent
sc-operator. -/
def piOp (p : V2) : ScOperator E E where
  lvl m := ContinuousLinearMap.prodMap (dρ p) (0 : Z2 m →L[ℝ] Z2 m)
  incl_comm m _ := Prod.ext rfl (by
    change Z2.incl m 0 = 0
    exact map_zero _)

lemma piOp_apply (p : V2) (q : E 0) : piOp p 0 q = ((dρ p q.1, 0) : E 0) := rfl

lemma piOp_idem {p : V2} (hp : p ∈ arc) (q : E 0) : piOp p 0 (piOp p 0 q) = piOp p 0 q :=
  Prod.ext (dρ_idem hp q.1) rfl

/-! ### The retraction of the chart model of `M` -/

lemma RM_mem_Udom {q : E 0} (hq : q ∈ Udom) : prM 0 (base q) ∈ Udom :=
  base_mem_Udom hq

/-- **`RM (p, a, b) = (ρ p, 0, 0)`**, an sc-smooth retraction of `U = C \ {p = 0}` onto the chart
model `arc × {0}` of `M`. -/
def RM : ScRetraction E (quadrant 2 Z2 0) where
  U := Udom
  toFun q := prM 0 (base q)
  relOpen := isRelOpen_Udom
  mapsTo q hq := RM_mem_Udom hq
  isScSmooth := IsScSmooth.comp isRelOpen_Udom.isScDomain (isScDomain_univ _)
    (prM.isScSmooth (isScDomain_univ _)) isScSmooth_base (mapsTo_univ _ _)
  idem q hq := by
    change ((ρ (ρ q.1), 0) : E 0) = (ρ q.1, 0)
    rw [ρ_ρ hq.1]

lemma RM_apply (q : E 0) : RM q = ((ρ q.1, 0) : E 0) := rfl

/-- The chart model of `M`: `arc × {0}`. -/
def Marc : Set (E 0) := {q | q.1 ∈ arc ∧ q.2 = 0}

lemma RM_retract : RM.retract = Marc := by
  ext q
  constructor
  · rintro ⟨q', hq', rfl⟩
    exact ⟨⟨fun i => ρ_nonneg hq'.2 hq'.1 i, len_ρ hq'.1⟩, rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨q, ⟨ne_zero_of_mem_arc h1, h1.1⟩, ?_⟩
    rw [RM_apply, ρ_of_mem_arc h1, ← h2]

lemma mem_Xs_of_mem_Icc {t : ℝ} (ht : t ∈ Icc (-1) 1) : (t, (0 : ℂ)) ∈ Xs := by
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc ht with h | h | h
  · rw [h]; exact mem_Xs_iff.2 (Or.inl rfl)
  · rw [h]; exact mem_Xs_iff.2 (Or.inr (Or.inl rfl))
  · exact mem_Xs_iff.2 (Or.inr (Or.inr ⟨h, by simp⟩))

lemma chart_of_mem_M {x : XR} (hx : x ∈ Mset) : chart x = ((arcPt x.1.1, 0) : E 0) := by
  rw [chart_apply, ψfun, show x.1.2 = 0 from hx, wdisk_zero, Complex.zero_re, Complex.zero_im,
    zero_smul]
  rfl

lemma chart_image_M : chart '' Mset = Marc := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [chart_of_mem_M hx]
    exact ⟨arcPt_mem_arc (fst_mem_Icc_of_mem x.2), rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨(tOf q.1, 0), mem_Xs_of_mem_Icc (tOf_mem_Icc h1)⟩, rfl, ?_⟩
    rw [chart_of_mem_M rfl]
    exact Prod.ext (arcPt_tOf h1) h2.symm

lemma shrink_mData : mData.toSubData.shrink chart = univ :=
  eq_univ_of_forall fun _ => ⟨⟨mem_univ _, mem_univ _⟩, mem_univ _, mem_univ _⟩

lemma chart_image_shrink_M : chart '' (mData.toSubData.shrink chart ∩ Mset) = RM.retract := by
  rw [shrink_mData, univ_inter, chart_image_M, RM_retract]

/-- The derivative of `RM` at `(p, 0, 0)` with `p` on the quarter circle. -/
theorem hasFDerivAt_RM {p : V2} (hp : p ∈ arc) (w : Z2 0) :
    HasFDerivAt RM (piOp p 0) ((p, w) : E 0) := by
  have hf : HasFDerivAt (Prod.fst : E 0 → V2) (ContinuousLinearMap.fst ℝ V2 (Z2 0))
      ((p, w) : E 0) := hasFDerivAt_fst
  have h1 : HasFDerivAt (fun q : E 0 => ρ q.1) ((dρ p).comp (ContinuousLinearMap.fst ℝ V2 (Z2 0)))
      ((p, w) : E 0) := by
    have h := HasFDerivAt.comp (g := ρ) ((p, w) : E 0) (hasFDerivAt_ρ hp) hf
    exact h
  have h2 := h1.prodMk (hasFDerivAt_const (0 : Z2 0) ((p, w) : E 0))
  exact h2

/-- **`scDeriv RM` at a point over `(p, 0, 0)`** is `piOp p`. -/
theorem scDeriv_RM {z : E 1} {p : V2} (hp : p ∈ arc) (hz : E.toBase 1 z = ((p, 0) : E 0)) :
    scDeriv RM.U RM z = piOp p 0 := by
  have hzU : z ∈ E.lvlSet RM.U 1 := by
    rw [ScBanach.mem_lvlSet, hz]; exact ⟨ne_zero_of_mem_arc hp, hp.1⟩
  refine scDeriv_eq_of_hasFDerivAt RM.relOpen RM.isSc1 hzU ?_
  rw [hz]
  exact hasFDerivAt_RM hp 0

lemma range_piOp {p : V2} (hp : p ∈ arc) :
    LinearMap.range (piOp p 0 : E 0 →ₗ[ℝ] E 0) = span ℝ {((Jp p, 0) : E 0)} := by
  ext v
  rw [LinearMap.mem_range, mem_span_singleton]
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨(1 / 4 : ℝ) * (-(p 1) * q.1 0 + p 0 * q.1 1), ?_⟩
    change _ = ((dρ p q.1, 0) : E 0)
    rw [dρ_eq_smul_Jp hp, Prod.smul_mk, smul_zero]
  · rintro ⟨c, rfl⟩
    refine ⟨c • ((Jp p, 0) : E 0), ?_⟩
    change ((dρ p (c • Jp p), 0) : E 0) = c • ((Jp p, 0) : E 0)
    rw [map_smul, dρ_Jp, Prod.smul_mk, smul_zero]

lemma finrank_range_piOp {p : V2} (hp : p ∈ arc) :
    finrank ℝ (LinearMap.range (piOp p 0 : E 0 →ₗ[ℝ] E 0)) = 1 := by
  rw [range_piOp hp, finrank_span_singleton]
  intro h
  exact Jp_ne_zero hp (congrArg Prod.fst h)

/-- **The tangent space of the chart model of `M`** at `(p, 0, 0)`: the line `ℝ (J p, 0)`. -/
theorem tangentSpace_Marc {z : E 1} {p : V2} (hp : p ∈ arc) (hz : E.toBase 1 z = ((p, 0) : E 0)) :
    tangentSpace E (quadrant 2 Z2 0) RM.retract z =
      (LinearMap.range (piOp p 0 : E 0 →ₗ[ℝ] E 0) : Set (E 0)) := by
  have hz' : z ∈ E.lvlSet RM.retract 1 := by
    rw [ScBanach.mem_lvlSet, hz, RM_retract]; exact ⟨hp, rfl⟩
  rw [tangentSpace_eq_coe_submodule RM hz', scDeriv_RM hp hz]

lemma toBase_levelLift_M {x : XR} (hx : x ∈ Mset) :
    chart.model.E.toBase 1 (levelLift chart 1 x) = chart x :=
  P.toBase_levelLift isChart_chart (mem_univ x)
    (P.smoothSet_subset_levelSet 1 (mem_smoothSet_of_snd_eq_zero hx))

lemma levelLift_M {x : XR} (hx : x ∈ Mset) :
    E.toBase 1 (levelLift chart 1 x) = ((arcPt x.1.1, 0) : E 0) :=
  (toBase_levelLift_M hx).trans (chart_of_mem_M hx)

/-- **`M` is a `1`-dimensional submanifold of `X`** (Remark 9.1.1). -/
theorem isSubmanifoldOfDim_M : P.IsSubmanifoldOfDim Mset 1 := by
  refine ⟨isSmoothSubmanifold_M, fun a ha => ?_⟩
  have hp := arcPt_mem_arc (fst_mem_Icc_of_mem a.2)
  have hQ : IsScRetract chart.model.E chart.model.C (chart '' (univ ∩ Mset)) := by
    rw [univ_inter, chart_image_M, ← RM_retract]; exact RM.isScRetract
  refine hasDimAt_of_finrank isSmoothSubmanifold_M ha isChart_chart isOpen_univ
    (subset_univ _) hQ (mem_univ a) (toBase_levelLift_M ha) ?_
  erw [univ_inter, chart_image_M, ← RM_retract, tangentSpace_Marc hp (levelLift_M ha), span_eq]
  exact finrank_range_piOp hp


lemma hrefl : quadrant 2 Z2 0 = (ScIso.refl E) 0 ⁻¹' quadrant 2 Z2 0 := by ext; rfl

/-- **`RM` is a tame retraction** (Definition 2.5.2): it keeps `d_C`, and at `(p, 0, 0)` the
kernel `ℝp ⊕ (X_w ⊕ X_w)` of its derivative is an sc-complement of `T_{(p,0,0)}(arc × {0})`
inside `E_{(p,0,0)}`. -/
theorem RM_isTameWith : RM.IsTameWith (ScIso.refl E) where
  degIndex_apply q hq := by
    rw [degIndex_quadrant (RM.mapsTo hq).2, degIndex_quadrant hq.2, quadrantDeg, quadrantDeg]
    congr 1
    refine Finset.filter_congr fun i _ => ?_
    change 2 / len q.1 * q.1 i = 0 ↔ q.1 i = 0
    have hl : 2 / len q.1 ≠ 0 := div_ne_zero two_ne_zero (len_pos hq.1).ne'
    exact ⟨fun h => (mul_eq_zero.1 h).resolve_left hl, fun h => by rw [h, mul_zero]⟩
  exists_complement x hx _ := by
    rw [ScBanach.mem_lvlSet, RM_retract] at hx
    set p := (E.toBase 1 x).1
    have hp : p ∈ arc := hx.1
    have hz : E.toBase 1 x = ((p, 0) : E 0) := Prod.ext rfl hx.2
    refine ⟨LinearMap.ker (piOp p 0 : E 0 →ₗ[ℝ] E 0), ?_, fun v hv => ?_⟩
    · rw [scDeriv_RM hp hz]
      exact ScBanach.isScSplitting_of_idem (piOp p) (piOp_idem hp)
    · have hv' : dρ p v.1 = 0 := congrArg Prod.fst (show piOp p 0 v = 0 from hv)
      rw [mem_minimalSubspaceWith]
      intro i hi
      change v.1 i = 0
      change (E.toBase 1 x).1 i = 0 at hi
      rw [eq_smul_of_dρ_eq_zero hv']
      change (1 / 4 * ellP p v.1) * p i = 0
      rw [show p i = 0 from hi, mul_zero]

/-- The chart model `arc × {0}` of `M` is a tame retract. -/
theorem isTameRetract_Marc : IsTameRetract E (quadrant 2 Z2 0) RM.retract :=
  ⟨RM, rfl, RM_isTameWith.isTame hrefl⟩

/-- **The structure induced on `M` is tame** (2021 Definition 2.5.18): its charts, the
restrictions of the chart of `X`, are modelled on the tame retract `arc × {0}`; at the points
`(±1, 0)` this is the end point of the quarter circle. -/
theorem hasTameInducedStructure_M : P.HasTameInducedStructure Mset := by
  refine ⟨isSmoothSubmanifold_M.isSubMPolyfold, ?_⟩
  let _ := P.paracompactSpace_subtype Mset
  refine isTame_of_forall_exists_chart _ fun a => ⟨subChart mData.toSubData isChart_chart a,
    subPolyfold_isChart _ mData.toSubData isChart_chart a, ?_, ?_⟩
  · change a.1 ∈ mData.toSubData.shrink chart
    rw [shrink_mData]; exact mem_univ _
  · have h : IsTameRetract chart.model.E chart.model.C
        (chart '' (mData.toSubData.shrink chart ∩ Mset)) := by
      rw [chart_image_shrink_M]; exact isTameRetract_Marc
    exact h


end DimensionJump

end Polyfold
