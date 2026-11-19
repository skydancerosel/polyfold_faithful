import Polyfold.Chapter9.DimensionJumpSheet
import Polyfold.Chapter4.BoundaryFormsAgreement
import Polyfold.Chapter9.HalfCircleWitness

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, §9.5,
**Remark 9.5.20** (pp. 451–452; 2017: Remark 9.8), point G.110: the branched ep⁺-subgroupoid
`Θ(t, z) = δ₀(z)` of `ℤ/3 ⋉ X` and its orientation.

# `Θ = 1_M` is a compact oriented tame branched ep⁺-subgroupoid of `ℤ/3 ⋉ X`

## The text, paraphrased
(p. 451) On `ℤ/3 ⋉ X` take `Θ(t, z) = δ₀(z)`, i.e. `Θ = 1` on `M = [−1, 1] × {0}` and `0`
elsewhere; it is oriented by the standard orientation of `[−1, 1]`.

## What is formalized
In the namespace `Polyfold.DimensionJump`.
* `tangentMor_of_mem_M`: for every morphism `(k, y)`, `y ∈ M`, the tangent map fixes `T_yM`
  (near `y` the local diffeomorphism of `(k, y)` is the rotation `k • ·`, which in the chart is
  the sc-operator `rotOp k` fixing `arc × {0}` and its tangent lines).
* `oM`: the orientation of `M` whose positive frames have chart vector a positive multiple of
  `(J p, 0)`, `p = arcPt t`, `J p = (−p₁, p₀)` (the direction of increasing `t`).
* `thetaM = 1_M`, `TM y = T_y(M, o)` on `M`:
  **`isBranchedEpSubgroupoid_thetaM`**, **`isCompactBranched_thetaM`**,
  **`isOrientation_thetaM`** (Definitions 9.1.2, 9.1.6, 9.3.2) in `ℤ/3 ⋉ X`;
* `mTame`, **`m_hloc`**, `m_hloc_LUC`: "oriented, tame" (an oriented tame structure of
  dimension `1` describing `T̂` at every point of `M`), also with LUC.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology Module Submodule
open scoped ContDiff Real

noncomputable section

namespace Polyfold

namespace DimensionJump

open DimensionJump
open ScOneExample hiding E

open RemarkFourThree MPolyfold EpGroupoid EpGroupoid.Examples

/-- The chart vectors of `T_yM` have vanishing `Z2`-component. -/
lemma chartVec_snd_eq_zero {y : XR} (hy : y ∈ Mset) {α : P.TangentSpace}
    (hα : α ∈ P.submanifoldTangent Mset y) : (chartVec isChart_chart α).2 = 0 := by
  have hp := arcPt_mem_arc (fst_mem_Icc_of_mem y.2)
  have h1 : chartVec isChart_chart α ∈ chartVec isChart_chart '' P.submanifoldTangent Mset y :=
    ⟨α, hα, rfl⟩
  rw [chartVec_image_submanifoldTangent isChart_chart mData hy (mem_univ y) (mem_univ y)] at h1
  have h2 : chart '' (mData.toSubData.shrink chart ∩ Mset) = RM.retract := chart_image_shrink_M
  erw [h2, tangentSpace_Marc hp (levelLift_M hy)] at h1
  obtain ⟨q, hq⟩ := h1
  rw [← hq]
  rfl

lemma rotOp_fix_zero (k : Z3) (q : E 0) (hq : q.2 = 0) : rotOp k 0 q = q := by
  rw [rotOp_apply]
  obtain ⟨a, b⟩ := q
  simp only at hq
  subst hq
  simp

lemma rotOp_one_fix (k : Z3) (z : E 1) (hz : (E.toBase 1 z).2 = 0) : rotOp k 1 z = z := by
  apply E.toBase_injective 1
  rw [ScOperator.toBase_comm, rotOp_fix_zero k _ hz]

/-- Near `y`, the local diffeomorphism `φ̂` of `φ = (k, y)` is the rotation `k • ·`. -/
lemma exists_eqOn_hat (k : Z3) (y : XR) : ∃ W : Set XR, IsOpen W ∧ y ∈ W ∧
    W ⊆ (ε.sheetAt (k, y)).srcSet ∧ EqOn (ε.hat (k, y)) (fun z => k • z) W := by
  set S := ε.sheetAt (k, y)
  have hd := S.isScDiffeoOn_src
  refine ⟨S.srcSet ∩ S.srcInv ⁻¹' {φ | φ.1 = k}, ?_, ⟨ε.src_mem_sheetAt (k, y), ?_⟩,
    inter_subset_left, ?_⟩
  · exact hd.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage hd.isScSmoothOn_inv.isOpen
      ((isOpen_discrete ({k} : Set Z3)).preimage continuous_fst)
  · change (S.srcInv (ε.src (k, y))).1 = k
    rw [hd.left_inv _ (ε.mem_sheetAt (k, y))]
  · rintro z ⟨hz, hk⟩
    change ε.tgt (S.srcInv z) = k • z
    have h2 : ε.src (S.srcInv z) = z := hd.right_inv z hz
    rw [ε_tgt, show (S.srcInv z).1 = k from hk]
    exact congrArg (k • ·) h2


/-- **`Tφ` fixes `T_yM`** for every morphism `φ = (k, y)` with `y ∈ M`: near `y` the local
diffeomorphism of `φ` is the rotation `k • ·`, which in the chart is the sc-operator `rotOp k`
fixing `arc × {0}` and its tangent lines. -/
theorem tangentMor_of_mem_M (k : Z3) {y : XR} (hy : y ∈ Mset) {α : P.TangentSpace}
    (hα : α ∈ P.submanifoldTangent Mset y) : ε.tangentMor (k, y) α = α := by
  have hy1 : y ∈ P.levelSet 1 :=
    P.smoothSet_subset_levelSet 1 (mem_smoothSet_of_snd_eq_zero hy)
  have hφ1 : (k, y) ∈ ε.PMor.levelSet 1 := (ε.mem_levelSet_src_iff (k, y) 1).1 hy1
  rw [ε.tangentMor_eq_tangentMapOn_hat hφ1 hα.1]
  obtain ⟨W, hW, hyW, hWS, heq⟩ := exists_eqOn_hat k y
  have hαW : α ∈ P.tangentPreimage W := by
    change P.levelVal 1 (P.tangentProj α) ∈ W
    rw [hα.1]; exact hyW
  refine (tangentMapOn_congr (ε.isScDiffeoOn_hat (k, y)).isScSmoothOn (isScSmoothMap_smul k) hW
    hWS (subset_univ _) heq hαW).trans ?_
  change tangentMapOn (isScSmoothMap_smul k) α = α
  rw [tangentMapOn_univ]
  have hm : ∀ β : P.TangentSpace, β ∈ tangentChartSet chart := fun _ => mem_univ _
  apply tangentChartMap_injOn isChart_chart (hm _) (hm _)
  rw [tangentChartMap_tangentMap_of_linear (isScSmoothMap_smul k) isChart_chart isChart_chart
    (rotOp k) (fun _ _ => mem_univ _) (fun x _ => chart_smul k x) (hm α)]
  refine Prod.ext (rotOp_one_fix k _ ?_) (rotOp_fix_zero k _ (chartVec_snd_eq_zero hy hα))
  rw [tangentChartMap_fst isChart_chart (hm α), hα.1, levelLift_M hy]

/-! ### The orientation of `M` -/

/-- **The tangent line of `M`**: in the chart, the chart vectors of `T_yM` form the line
`ℝ (J p, 0)`, `p = arcPt t`, `J p = (−p₁, p₀)`. -/
theorem chartVec_image_M {y : XR} (hy : y ∈ Mset) :
    chartVec isChart_chart '' P.submanifoldTangent Mset y =
      (span ℝ {((Jp (arcPt y.1.1), 0) : E 0)} : Set (E 0)) := by
  have hp := arcPt_mem_arc (fst_mem_Icc_of_mem y.2)
  rw [chartVec_image_submanifoldTangent isChart_chart mData hy (mem_univ y) (mem_univ y)]
  have h2 : chart '' (mData.toSubData.shrink chart ∩ Mset) = RM.retract := chart_image_shrink_M
  erw [h2, tangentSpace_Marc hp (levelLift_M hy), range_piOp hp]

/-- The frame `(J p, 0)` of `T_yM`, `p = arcPt t`: the velocity of `t ↦ (t, 0)` up to the factor
`π/4`. -/
def frameVecM (y : XR) : Fin 1 → E 0 := fun _ => ((Jp (arcPt y.1.1), 0) : E 0)

theorem frameVecM_ne_zero (y : XR) (i : Fin 1) : frameVecM y i ≠ 0 := fun h => by
  have h1 := congrArg Prod.fst h
  exact Jp_ne_zero (arcPt_mem_arc (fst_mem_Icc_of_mem y.2)) h1

theorem linearIndependent_frameVecM (y : XR) : LinearIndependent ℝ (frameVecM y) :=
  linearIndependent_unique_iff.2 (frameVecM_ne_zero y default)

/-- The line spanned by the frame. -/
abbrev NM (y : XR) : Submodule ℝ (E 0) := span ℝ (range (frameVecM y))

theorem range_frameVecM (y : XR) : range (frameVecM y) = {((Jp (arcPt y.1.1), 0) : E 0)} :=
  range_const

theorem NM_eq {y : XR} (hy : y ∈ Mset) :
    (NM y : Set (E 0)) = chartVec isChart_chart '' P.submanifoldTangent Mset y := by
  rw [chartVec_image_M hy, NM, range_frameVecM]

/-- The frames of `T_yM` positive for the orientation given by `(J p, 0)`. -/
def framesM (y : XR) : Set (Fin 1 → P.TangentSpace) :=
  {v | (∀ i, v i ∈ P.submanifoldTangent Mset y) ∧ ∃ b : Basis (Fin 1) ℝ (NM y),
    (∀ i, (b i : E 0) = chartVec isChart_chart (v i)) ∧
      b.orientation = (Basis.span (linearIndependent_frameVecM y)).orientation}

theorem isChartOrientation_M {y : XR} (hy : y ∈ Mset) :
    IsChartOrientation isChart_chart ⟨1, P.submanifoldTangent Mset y, framesM y⟩ := by
  refine ⟨NM y, NM_eq hy, FiniteDimensional.span_of_finite ℝ (finite_range _), ?_,
    (Basis.span (linearIndependent_frameVecM y)).orientation, rfl⟩
  change finrank ℝ (NM y) = 1
  rw [NM, finrank_span_eq_card (linearIndependent_frameVecM y), Fintype.card_fin]

theorem continuous_Jp : Continuous Jp := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact (continuous_apply 1).neg
  · exact continuous_apply 0

theorem continuous_frameVecM : Continuous fun (y : XR) (i : Fin 1) => frameVecM y i :=
  continuous_pi fun _ => ((continuous_Jp.comp (continuous_arcPt.comp
    (continuous_fst.comp continuous_subtype_val))).prodMk continuous_const)

/-- **The orientation of `M` by the standard orientation of `[−1, 1]`** (Remark 9.5.20, p. 451):
positive frames are those whose chart vector is a positive multiple of `(J p, 0)`, the direction
of increasing `t`. -/
def oM : P.SubmanifoldOrientation Mset 1 where
  frames := framesM
  isOrientedAt _ hy := ⟨fun _ hα => hα.1, chart, isChart_chart, mem_univ _,
    isChartOrientation_M hy⟩
  continuous _ y hy := by
    have hlift : ∀ y' ∈ Mset, ∀ i : Fin 1, ∃ α ∈ P.submanifoldTangent Mset y',
        chartVec isChart_chart α = frameVecM y' i := fun y' hy' i => by
      have : frameVecM y' i ∈ chartVec isChart_chart '' P.submanifoldTangent Mset y' := by
        rw [← NM_eq hy']
        exact subset_span (mem_range_self i)
      exact this
    obtain ⟨α₀, -, -⟩ := hlift y hy 0
    have : Nonempty P.TangentSpace := ⟨α₀⟩
    choose! e he1 he2 using hlift
    refine ⟨chart, isChart_chart, univ, isOpen_univ, mem_univ y, subset_univ _,
      fun y' i => e y' i, fun y' hy' => ⟨fun i => he1 y' hy'.1 i,
        Basis.span (linearIndependent_frameVecM y'), fun i => ?_, rfl⟩, ?_⟩
    · exact (congrArg Subtype.val (Basis.span_apply (linearIndependent_frameVecM y') i)).trans
        (he2 y' hy'.1 i).symm
    · exact continuous_frameVecM.continuousOn.congr fun y' hy' =>
        funext fun i => he2 y' hy'.1 i

/-! ### `Θ = 1_M` and its oriented tangent sums -/

lemma isClosed_M : IsClosed Mset :=
  isClosed_eq (continuous_snd.comp continuous_subtype_val) continuous_const

/-- The parametrization `t ↦ (t, 0)` of `M` by `[−1, 1]`. -/
def mPar (t : Icc (-1 : ℝ) 1) : XR := ⟨(t.1, 0), mem_Xs_of_mem_Icc t.2⟩

lemma continuous_mPar : Continuous mPar :=
  Continuous.subtype_mk ((continuous_subtype_val).prodMk continuous_const) _

lemma range_mPar : range mPar = Mset := by
  ext y
  refine ⟨?_, fun hy => ⟨⟨y.1.1, fst_mem_Icc_of_mem y.2⟩, ?_⟩⟩
  · rintro ⟨t, rfl⟩; rfl
  · exact Subtype.ext (Prod.ext rfl hy.symm)

lemma isCompact_M : IsCompact Mset := by
  rw [← range_mPar]
  have : CompactSpace (Icc (-1 : ℝ) 1) := isCompact_iff_compactSpace.1 isCompact_Icc
  exact isCompact_range continuous_mPar

lemma smul_mem_M_iff (k : Z3) (y : XR) : k • y ∈ Mset ↔ y ∈ Mset := by
  change (rotC k * y.1.2 = 0) ↔ y.1.2 = 0
  have : rotC k ≠ 0 := fun h => by simpa [h] using norm_rotC k
  simp [this]

open scoped Classical in
/-- **`Θ = 1_M`** (Remark 9.5.20, p. 451: `Θ(t, z) = δ₀(z)`). -/
def thetaM (y : XR) : ℚ := if y ∈ Mset then 1 else 0

open scoped Classical in
/-- `T̂(y) = T_y(M, o)` for `y ∈ M`, `0` otherwise. -/
def TM (y : XR) : P.OrTangent →₀ ℚ :=
  if y ∈ Mset then Finsupp.single (oM.tangent y) 1 else 0

theorem supp_thetaM : supp thetaM = Mset := by
  ext y
  change 0 < thetaM y ↔ _
  by_cases hy : y ∈ Mset <;> simp [thetaM, hy]

/-- **The oriented local branching structure of `Θ` at `x ∈ M`** on an open `W ∋ x`: the one
sheet `M ∩ W`, weight `1`, the restricted orientation. -/
def mBranching {x : XR} (hx : x ∈ Mset) {W : Set XR} (hW : IsOpen W) (hxW : x ∈ W) :
    ε.OrientedBranchingStructure thetaM x where
  U := W
  isOpen_U := hW
  mem_U := hxW
  ι := Unit
  M _ := Mset ∩ W
  subset_U _ := inter_subset_right
  isSmoothSubmanifold _ := isSmoothSubmanifold_M.inter_isOpen hW
  mem_M _ := ⟨hx, hxW⟩
  isProperMap _ := by
    refine (isProperMap_inclusion_iff _).2 ?_
    convert isClosed_M.preimage continuous_subtype_val using 1
    ext y
    exact ⟨fun h => h.1, fun h => ⟨h, y.2⟩⟩
  σ _ := 1
  σ_pos _ := one_pos
  eq_sum y hy := by
    by_cases h : y ∈ Mset
    · simp [thetaM, h, hy]
    · simp [thetaM, h]
  dim _ := 1
  isSubmanifoldOfDim _ := isSubmanifoldOfDim_M.inter_isOpen hW
  orient _ := oM.restrict hW

theorem mBranching_orientedSum {x : XR} (hx : x ∈ Mset) {W : Set XR} (hW : IsOpen W)
    (hxW : x ∈ W) {y : XR} (hy : y ∈ W) : (mBranching hx hW hxW).orientedSum y = TM y := by
  have : Unique (mBranching hx hW hxW).ι := inferInstanceAs (Unique Unit)
  rw [OrientedBranchingStructure.orientedSum, Finset.sum_filter, Fintype.sum_unique, TM]
  by_cases h : y ∈ Mset
  · rw [if_pos (show y ∈ (mBranching hx hW hxW).M default from ⟨h, hy⟩), if_pos h]
    exact congrArg (fun g => Finsupp.single g (1 : ℚ)) (oM.restrict_tangent hW hy)
  · rw [if_neg (show y ∉ (mBranching hx hW hxW).M default from fun h' => h h'.1), if_neg h]
    rfl

theorem TM_mem_GrHat (y : XR) : TM y ∈ ε.GrHat y := by
  by_cases h : y ∈ Mset
  · rw [← mBranching_orientedSum h isOpen_univ (mem_univ y) (mem_univ y)]
    exact OrientedBranchingStructure.orientedSum_mem _ y
  · rw [TM, if_neg h]
    exact zero_mem_GrHat y

/-! ### Branched, compact, oriented -/

/-- **`Θ = 1_M` is a branched ep⁺-subgroupoid of `ℤ/3 ⋉ X`** (Definition 9.1.2). -/
theorem isBranchedEpSubgroupoid_thetaM : ε.IsBranchedEpSubgroupoid thetaM where
  nonneg y := by unfold thetaM; split_ifs <;> norm_num
  isFunctorial φ := by
    change thetaM φ.2 = thetaM (φ.1 • φ.2)
    by_cases h : φ.2 ∈ Mset
    · rw [thetaM, thetaM, if_pos h, if_pos ((smul_mem_M_iff _ _).2 h)]
    · rw [thetaM, thetaM, if_neg h, if_neg fun h' => h ((smul_mem_M_iff _ _).1 h')]
  support_subset y hy := by
    rw [supp_thetaM] at hy
    exact mem_smoothSet_of_snd_eq_zero hy
  paracompactSpace_orbitSupp := by
    have hc : IsCompact (ε.orbitSupp thetaM) := by
      unfold orbitSupp
      rw [supp_thetaM]
      exact isCompact_M.image ε.continuous_π
    have := isCompact_iff_compactSpace.1 hc
    infer_instance
  localBranching x hx := by
    rw [supp_thetaM] at hx
    exact ⟨(mBranching hx isOpen_univ (mem_univ x)).toLocalBranchingStructure⟩

/-- **`Θ` is compact** (Definition 9.1.6 (2)): `|supp Θ| = π(M)`. -/
theorem isCompactBranched_thetaM : ε.IsCompactBranched thetaM := by
  unfold IsCompactBranched orbitSupp
  rw [supp_thetaM]
  exact isCompact_M.image ε.continuous_π

theorem hasIndependentTangentSums_thetaM : ε.HasIndependentTangentSums thetaM := by
  refine hasIndependentTangentSums_of_subset_goodSet fun y hy => ?_
  refine (mem_goodSet_iff isBranchedEpSubgroupoid_thetaM).2 ⟨hy, univ, univ_mem, fun z _ hz => ?_⟩
  rw [supp_thetaM] at hy hz
  simp [thetaM, hy, hz]

/-- **`T̂` is natural**: the tangent maps of the morphisms `(k, y)`, `y ∈ M`, fix `T_y(M, o)`. -/
theorem grHatPush_TM (φ : Z3 × XR) : ε.grHatPush φ (TM (ε.src φ)) = TM (ε.tgt φ) := by
  obtain ⟨k, y⟩ := φ
  change ε.grHatPush (k, y) (TM y) = TM (k • y)
  by_cases hy : y ∈ Mset
  · rw [smul_eq_self_of_snd_eq_zero k hy, TM, if_pos hy]
    change Finsupp.mapDomain _ _ = _
    erw [Finsupp.mapDomain_single]
    congr 1
    refine (MPolyfold.OrTangent.push_congr (f' := id) (g := oM.tangent y)
      (fun α (hα : α ∈ P.submanifoldTangent Mset y) => tangentMor_of_mem_M k hy hα)
      fun v (hv : v ∈ framesM y) i => hv.1 i).trans ?_
    exact MPolyfold.OrTangent.push_id _
  · rw [TM, if_neg hy, TM, if_neg (by rwa [smul_mem_M_iff])]
    exact Finsupp.mapDomain_zero

/-- **`T̂` is an orientation of `Θ`** (Definition 9.3.2). -/
theorem isOrientation_thetaM : ε.IsOrientation thetaM TM :=
  IsOrientation.mk' hasIndependentTangentSums_thetaM (fun y _ => TM_mem_GrHat y)
    (fun φ _ => grHatPush_TM φ)
    (fun y _ hy => by
      rw [supp_thetaM] at hy
      rw [TM, if_neg hy]
      rfl)
    fun x hx => by
      rw [supp_thetaM] at hx
      exact ⟨mBranching hx isOpen_univ (mem_univ x), fun y hy _ =>
        (mBranching_orientedSum hx isOpen_univ (mem_univ x) hy).symm⟩

/-! ### Oriented tame structures -/

/-- **The object `ℤ/3 ⋉ X` of `EP`.** -/
abbrev AX : EP.{0} := EP.mk XR (Z3 × XR) ε

/-- **The oriented tame structure at `x ∈ M`** on the domain of a natural representation `R`. -/
def mTame {x : XR} (hx : x ∈ Mset) (R : ε.NaturalRep x) :
    ε.OrientedTameStructure (0 + 1) thetaM x where
  toLocalBranchingStructure := (mBranching hx R.isOpen_U R.mem_U).toLocalBranchingStructure
  rep := R
  U_eq := rfl
  hasPropernessProperty := hasPropernessProperty_action isScSmoothMap_smul R.isOpen_U
  hasTameInducedStructure _ :=
    HasTameInducedStructure.inter_isOpen isSmoothSubmanifold_M hasTameInducedStructure_M
      R.isOpen_U
  isSubmanifoldOfDim _ := isSubmanifoldOfDim_M.inter_isOpen R.isOpen_U
  orient _ := oM.restrict R.isOpen_U

theorem mTame_represents {x : XR} (hx : x ∈ Mset) (R : ε.NaturalRep x) :
    (mTame hx R).Represents TM := fun _ hy _ =>
  (mBranching_orientedSum hx R.isOpen_U R.mem_U hy).symm

/-- **"Oriented, tame" for `Θ = 1_M`**: an oriented tame structure of dimension `1` describing
`T̂` at every point of `supp Θ`. -/
theorem m_hloc : ∀ x ∈ supp thetaM, ∃ C : AX.X.OrientedTameStructure (0 + 1) thetaM x,
    C.Represents TM := by
  intro x hx
  rw [supp_thetaM] at hx
  obtain ⟨R, -⟩ := theorem_7_1_13 ε x isOpen_univ (mem_univ x)
  exact ⟨mTame hx R, mTame_represents hx R⟩

theorem m_hloc_LUC : ∀ x ∈ supp thetaM, ∃ C : AX.X.OrientedTameStructure (0 + 1) thetaM x,
    C.Represents TM ∧ C.rep.HasLUC :=
  AX.hloc_hasLUC_dim1 isLUC_ε m_hloc

end DimensionJump

end Polyfold
