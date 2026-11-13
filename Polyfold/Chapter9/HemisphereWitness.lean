import Polyfold.Chapter9.HemisphereSheet
import Polyfold.Chapter9.TameOpen
import Polyfold.Chapter9.FormEvalInfty
import Polyfold.Chapter9.MultiChartCompact
import Polyfold.Chapter9.MultiChartIntegration
import Polyfold.Chapter9.BoundarySheets
import Polyfold.Chapter7.LocalDiffeo

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, Theorems 9.5.17 and 9.5.18 (Stokes), the witness of their hypotheses
with `m = 1`.  Numbers and pages are the 2021 text's.

# A compact oriented `2`-dimensional witness with nonempty boundary

`X` is the trivial ep-groupoid of the half-space `[0, ∞) × ℝ²` (`Ph`, `HemisphereSheet`),
packaged as the object `AH` of `EP`, and `Θ = 1_{hemi}` (`thetaH`) for the closed upper
hemisphere `hemi`, oriented by the frames `(f₀(a), f₁(a))` of `SphereRadialRetraction`
(`hemiOrientation`), with `T̂(y) = T_y(hemi, o)` on `hemi` (`TH`).  Then:

* `e8w_hasScPartitionsOfUnity`: `X` has sc-smooth partitions of unity (Definition 7.5.5; the chart
  `id` of `ℝ³` has the approximation property, Theorem 5.5.10, Proposition 5.5.11);
* `e8w_isBranchedEpSubgroupoid`, `e8w_isCompactBranched`, `e8w_isOrientation`: Definitions 9.1.2,
  9.1.6, 9.3.2;
* `e8w_hcov`: every point of `supp Θ = hemi` has an oriented tame structure of dimension `2`
  (Definitions 9.3.3, 9.3.6) describing `T`, with its sheet `hemi ∩ U` in the class `sheets` of the
  `2`-forms `epFormsInftyEval 2` and its boundary sheet `∂₁(hemi ∩ U) = equator ∩ U` in the class
  `msheets` of the `1`-forms `epFormsInftyEval 1`;
* `e8w_boundary_nonempty`, `e8w_supp_nonempty`: `∂Θ(pt0) = 1` at the equator point
  `pt0 = (0, 1, 0)`, and `supp Θ ≠ ∅`;
* `e8w_stokes_hypotheses`: the conjunction.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology Module Submodule
open scoped ContDiff

noncomputable section

namespace Polyfold

open MPolyfold EpGroupoid

namespace E8W

/-! ### The orientation of the hemisphere -/

/-- The level-`1` lift of a point of `X` in the chart `id` is the point itself. -/
theorem levelLift_chartQ (z : Q3) : levelLift chartQ 1 z = lev1 z.1 :=
  (bijective_toBase_E3 1).1 ((Ph.toBase_levelLift isChart_chartQ (mem_univ z)
    (Ph_mem_levelSet 1 z)).trans (toBase_lev1 z.1).symm)

/-- **The tangent plane of `hemi`**: in the chart `id`, the chart vectors of `T_z hemi` form
`z^⊥`. -/
theorem chartVec_image_hemi {z : Q3} (hz : z ∈ hemi) :
    chartVec isChart_chartQ '' Ph.submanifoldTangent hemi z =
      (LinearMap.ker (ell z.1 : V3 →ₗ[ℝ] ℝ) : Set V3) := by
  rw [chartVec_image_submanifoldTangent isChart_chartQ hemiData hz (hemi_subset_Vh hz)
    (mem_univ z), levelLift_chartQ]
  erw [chartQ_image_shrink, tangentSpace_hemi ⟨hz, z.2⟩]

theorem one_add_pos_of_mem (z : Q3) : 0 < 1 + z.1.1 0 := by
  have : 0 ≤ z.1.1 0 := z.2 0
  linarith

theorem linearIndependent_frameVecQ (z : Q3) : LinearIndependent ℝ (frameVec z.1) :=
  linearIndependent_frameVec (one_add_pos_of_mem z)

/-- The plane spanned by the frame `(f₀(z), f₁(z))`. -/
def hemiN (z : Q3) : Submodule ℝ V3 := span ℝ (range (frameVec z.1))

theorem hemiN_eq {z : Q3} (hz : z ∈ hemi) :
    hemiN z = LinearMap.ker (ell z.1 : V3 →ₗ[ℝ] ℝ) := by
  refine Submodule.eq_of_le_of_finrank_eq (span_le.2 (range_subset_iff.2 fun i => ?_)) ?_
  · change ell z.1 (frameVec z.1 i) = 0
    rw [ell_apply]
    exact ell_frameVec hz (one_add_pos_of_mem z) i
  · rw [hemiN, finrank_span_eq_card (linearIndependent_frameVecQ z), finrank_ker_ell hz,
      Fintype.card_fin]

/-- The frames of `T_z hemi` positive for the orientation given by `(f₀(z), f₁(z))`. -/
def hemiFrames (z : Q3) : Set (Fin 2 → Ph.TangentSpace) :=
  {v | (∀ i, v i ∈ Ph.submanifoldTangent hemi z) ∧ ∃ b : Basis (Fin 2) ℝ (hemiN z),
    (∀ i, (b i : V3) = chartVec isChart_chartQ (v i)) ∧
      b.orientation = (Basis.span (linearIndependent_frameVecQ z)).orientation}

theorem isChartOrientation_hemi {z : Q3} (hz : z ∈ hemi) :
    IsChartOrientation isChart_chartQ ⟨2, Ph.submanifoldTangent hemi z, hemiFrames z⟩ := by
  refine ⟨hemiN z, ?_, FiniteDimensional.span_of_finite ℝ (finite_range _), ?_,
    (Basis.span (linearIndependent_frameVecQ z)).orientation, rfl⟩
  · change ((hemiN z : Set V3)) = _
    rw [chartVec_image_hemi hz, hemiN_eq hz]
  · change finrank ℝ (hemiN z) = 2
    rw [hemiN, finrank_span_eq_card (linearIndependent_frameVecQ z), Fintype.card_fin]

theorem continuousOn_frameVecQ :
    ContinuousOn (fun (z : Q3) (i : Fin 2) => frameVec z.1 i) univ := by
  refine continuousOn_pi.2 fun i => ?_
  have h := continuousOn_frameVec i
  refine (h.comp continuous_subtype_val.continuousOn fun z _ => ?_)
  exact one_add_pos_of_mem z

/-- **An orientation of the hemisphere** (Definition 9.3.3): positive frames those whose chart
vectors are a basis of `z^⊥` of the orientation of `(f₀(z), f₁(z))`; continuous since the
`f_i` are. -/
def hemiOrientation : Ph.SubmanifoldOrientation hemi 2 where
  frames := hemiFrames
  isOrientedAt _ hz := ⟨fun _ hα => hα.1, chartQ, isChart_chartQ, mem_univ _,
    isChartOrientation_hemi hz⟩
  continuous _ z hz := by
    have hlift : ∀ z' ∈ hemi, ∀ i : Fin 2, ∃ α ∈ Ph.submanifoldTangent hemi z',
        chartVec isChart_chartQ α = frameVec z'.1 i := fun z' hz' i => by
      have : frameVec z'.1 i ∈ chartVec isChart_chartQ '' Ph.submanifoldTangent hemi z' := by
        rw [chartVec_image_hemi hz', ← hemiN_eq hz']
        exact subset_span (mem_range_self i)
      exact this
    obtain ⟨α₀, -, -⟩ := hlift z hz 0
    have : Nonempty Ph.TangentSpace := ⟨α₀⟩
    choose! e he1 he2 using hlift
    refine ⟨chartQ, isChart_chartQ, univ, isOpen_univ, mem_univ z, subset_univ _,
      fun z' i => e z' i, fun z' hz' => ⟨fun i => he1 z' hz'.1 i,
        Basis.span (linearIndependent_frameVecQ z'), fun i => ?_, rfl⟩, ?_⟩
    · exact (congrArg Subtype.val (Basis.span_apply (linearIndependent_frameVecQ z') i)).trans
        (he2 z' hz'.1 i).symm
    · exact (continuousOn_frameVecQ.mono (subset_univ _)).congr fun z' hz' =>
        funext fun i => he2 z' hz'.1 i

/-! ### `Θ = 1_{hemi}` and its oriented tangent sums -/

open scoped Classical in
/-- `Θ = 1_{hemi}`. -/
def thetaH (y : Q3) : ℚ := if y ∈ hemi then 1 else 0

open scoped Classical in
/-- `T̂(y) = T_y(hemi, o)` for `y ∈ hemi`, `0` otherwise. -/
def TH (y : Q3) : Ph.OrTangent →₀ ℚ :=
  if y ∈ hemi then Finsupp.single (hemiOrientation.tangent y) 1 else 0

theorem supp_thetaH : supp thetaH = hemi := by
  ext y
  change 0 < thetaH y ↔ _
  by_cases hy : y ∈ hemi <;> simp [thetaH, hy]

/-- **The oriented local branching structure of `Θ` at `x ∈ hemi`** on an open `W ∋ x`: the one
sheet `hemi ∩ W`, weight `1`, the restricted orientation. -/
def hemiBranching {x : Q3} (hx : x ∈ hemi) {W : Set Q3} (hW : IsOpen W) (hxW : x ∈ W) :
    (trivial Ph).OrientedBranchingStructure thetaH x where
  U := W
  isOpen_U := hW
  mem_U := hxW
  ι := Unit
  M _ := hemi ∩ W
  subset_U _ := inter_subset_right
  isSmoothSubmanifold _ := isSmoothSubmanifold_hemi.inter_isOpen hW
  mem_M _ := ⟨hx, hxW⟩
  isProperMap _ := by
    refine (isProperMap_inclusion_iff _).2 ?_
    convert isClosed_hemi.preimage continuous_subtype_val using 1
    ext y
    exact ⟨fun h => h.1, fun h => ⟨h, y.2⟩⟩
  σ _ := 1
  σ_pos _ := one_pos
  eq_sum y hy := by
    by_cases h : y ∈ hemi
    · simp [thetaH, h, hy]
    · simp [thetaH, h]
  dim _ := 2
  isSubmanifoldOfDim _ := isSubmanifoldOfDim_hemi.inter_isOpen hW
  orient _ := hemiOrientation.restrict hW

theorem hemiBranching_orientedSum {x : Q3} (hx : x ∈ hemi) {W : Set Q3} (hW : IsOpen W)
    (hxW : x ∈ W) {y : Q3} (hy : y ∈ W) : (hemiBranching hx hW hxW).orientedSum y = TH y := by
  have : Unique (hemiBranching hx hW hxW).ι := inferInstanceAs (Unique Unit)
  rw [OrientedBranchingStructure.orientedSum, Finset.sum_filter, Fintype.sum_unique, TH]
  by_cases h : y ∈ hemi
  · rw [if_pos (show y ∈ (hemiBranching hx hW hxW).M default from ⟨h, hy⟩), if_pos h]
    exact congrArg (fun g => Finsupp.single g (1 : ℚ)) (hemiOrientation.restrict_tangent hW hy)
  · rw [if_neg (show y ∉ (hemiBranching hx hW hxW).M default from fun h' => h h'.1), if_neg h]
    rfl

theorem TH_mem_GrHat (y : Q3) : TH y ∈ (trivial Ph).GrHat y := by
  by_cases h : y ∈ hemi
  · rw [← hemiBranching_orientedSum h isOpen_univ (mem_univ y) (mem_univ y)]
    exact OrientedBranchingStructure.orientedSum_mem _ y
  · rw [TH, if_neg h]
    exact zero_mem_GrHat y

/-! ### Hypothesis 2: branched, compact, oriented -/

/-- **`Θ = 1_{hemi}` is a branched ep⁺-subgroupoid** (Definition 9.1.2). -/
theorem isBranchedEpSubgroupoid_thetaH : (trivial Ph).IsBranchedEpSubgroupoid thetaH where
  nonneg y := by unfold thetaH; split_ifs <;> norm_num
  isFunctorial _ := rfl
  support_subset y _ := Ph_mem_smoothSet y
  paracompactSpace_orbitSupp :=
    paracompactSpace_orbitSupp_trivial_of_isClosed Ph (by rw [supp_thetaH]; exact isClosed_hemi)
  localBranching x hx := by
    rw [supp_thetaH] at hx
    exact ⟨(hemiBranching hx isOpen_univ (mem_univ x)).toLocalBranchingStructure⟩

/-- **`Θ` is compact** (Definition 9.1.6 (2)): `|supp Θ| = π(hemi)`. -/
theorem isCompactBranched_thetaH : (trivial Ph).IsCompactBranched thetaH := by
  unfold IsCompactBranched orbitSupp
  rw [supp_thetaH]
  exact isCompact_hemi.image (trivial Ph).continuous_π

/-- Every point of `supp Θ` is good (`Θ = 1` on `supp Θ`), so the tangent sums are independent
(Theorem 9.2.1). -/
theorem hasIndependentTangentSums_thetaH : (trivial Ph).HasIndependentTangentSums thetaH := by
  refine hasIndependentTangentSums_of_subset_goodSet fun y hy => ?_
  refine (mem_goodSet_iff isBranchedEpSubgroupoid_thetaH).2 ⟨hy, univ, univ_mem, fun z _ hz => ?_⟩
  rw [supp_thetaH] at hy hz
  simp [thetaH, hy, hz]

/-- **`T̂` is an orientation of `Θ`** (Definition 9.3.2). -/
theorem isOrientation_thetaH : (trivial Ph).IsOrientation thetaH TH :=
  IsOrientation.mk' hasIndependentTangentSums_thetaH (fun y _ => TH_mem_GrHat y)
    (fun φ _ => grHatPush_unit (TH_mem_GrHat φ))
    (fun y _ hy => by
      rw [supp_thetaH] at hy
      rw [TH, if_neg hy]
      rfl)
    fun x hx => by
      rw [supp_thetaH] at hx
      exact ⟨hemiBranching hx isOpen_univ (mem_univ x), fun y hy _ =>
        (hemiBranching_orientedSum hx isOpen_univ (mem_univ x) hy).symm⟩

/-! ### Hypothesis 3: oriented tame structures with sheets in the classes -/

/-- The boundary stratum is local: `∂₁(A ∩ V) = ∂₁A ∩ V` for open `V`. -/
theorem boundaryStratum_inter_isOpen {A V : Set Q3} (hV : IsOpen V) :
    Ph.boundaryStratum (A ∩ V) = Ph.boundaryStratum A ∩ V := by
  ext y
  constructor
  · rintro ⟨⟨hyA, hyV⟩, h⟩
    exact ⟨⟨hyA, fun c => by rw [← submanifoldTangent_inter_isOpen hV hyV]; exact h c⟩, hyV⟩
  · rintro ⟨⟨hyA, h⟩, hyV⟩
    exact ⟨⟨hyA, hyV⟩, fun c => by rw [submanifoldTangent_inter_isOpen hV hyV]; exact h c⟩

/-- The equator `∂₁ hemi` is a `1`-dimensional submanifold (E6). -/
theorem isSubmanifoldOfDim_equator : Ph.IsSubmanifoldOfDim equator 1 := by
  rw [← boundaryStratum_hemi]
  exact isSubmanifoldOfDim_boundaryStratum isSubmanifoldOfDim_hemi hasTameInducedStructure_hemi

/-- **The object `X = [0, ∞) × ℝ²` (trivial ep-groupoid) of `EP`.** -/
abbrev AH : EP.{0} := EP.mk Q3 Q3 (trivial Ph)

/-- **The oriented tame structure at `x ∈ hemi`** on the domain of a natural representation `R`. -/
def hemiTame {x : Q3} (hx : x ∈ hemi) (R : (trivial Ph).NaturalRep x) :
    (trivial Ph).OrientedTameStructure 2 thetaH x where
  toLocalBranchingStructure := (hemiBranching hx R.isOpen_U R.mem_U).toLocalBranchingStructure
  rep := R
  U_eq := rfl
  hasPropernessProperty := hasPropernessProperty_trivial Ph R.isOpen_U
  hasTameInducedStructure _ :=
    HasTameInducedStructure.inter_isOpen isSmoothSubmanifold_hemi hasTameInducedStructure_hemi
      R.isOpen_U
  isSubmanifoldOfDim _ := isSubmanifoldOfDim_hemi.inter_isOpen R.isOpen_U
  orient _ := hemiOrientation.restrict R.isOpen_U

theorem hemiTame_represents {x : Q3} (hx : x ∈ hemi) (R : (trivial Ph).NaturalRep x) :
    (hemiTame hx R).Represents TH := fun _ hy _ =>
  (hemiBranching_orientedSum hx R.isOpen_U R.mem_U hy).symm

theorem hemiTame_boundarySheet {x : Q3} (hx : x ∈ hemi) (R : (trivial Ph).NaturalRep x)
    (i : Unit) : (hemiTame hx R).boundarySheet i = equator ∩ R.U := by
  change Ph.boundaryStratum (hemi ∩ R.U) = _
  rw [boundaryStratum_inter_isOpen R.isOpen_U, boundaryStratum_hemi]

/-- **Hypothesis 3 of Theorems 9.5.17, 9.5.18**: every `x ∈ supp Θ` has an oriented tame
structure of dimension `2` describing `T`, with sheets in the class `sheets` of the `2`-forms and
boundary sheets in the class `msheets` of the `1`-forms. -/
theorem e8w_hcov : ∀ x ∈ supp thetaH, ∃ C : AH.X.OrientedTameStructure 2 thetaH x,
    C.Represents TH ∧ (∀ i, C.M i ∈ (AH.epFormsInftyEval 2).sheets) ∧
      ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ (AH.epFormsInftyEval 1).msheets := by
  intro x hx
  rw [supp_thetaH] at hx
  obtain ⟨V, hV, hxV, hVS⟩ :=
    FormEval.exists_mem_sheets (F := AH.epFormsInftyEval 2) isSubmanifoldOfDim_hemi hx
  obtain ⟨R, hRV⟩ := theorem_7_1_13 (trivial Ph) x hV hxV
  refine ⟨hemiTame hx R, hemiTame_represents hx R, fun i => ?_, fun i _ => ?_⟩
  · have e : (hemiTame hx R).M i = (hemi ∩ V) ∩ R.U := by
      change hemi ∩ R.U = _
      rw [inter_assoc, inter_eq_right.2 hRV]
    rw [e]
    exact FormEval.inter_mem_sheets hVS R.isOpen_U
  · erw [hemiTame_boundarySheet]
    exact FormEval.msheets_inter_isOpen (FormEval.msheets_of_isCompact isSubmanifoldOfDim_equator
      isCompact_equator equator_nonempty) R.isOpen_U

/-! ### Nontriviality -/

theorem pt0_mem_hemi : pt0 ∈ hemi := pt0_mem_equator.1

/-- **`∂Θ(pt0) = 1`** at the equator point `pt0 = (0, 1, 0)`. -/
theorem boundaryTheta_pt0 : (trivial Ph).boundaryTheta thetaH pt0 = 1 := by
  classical
  rw [boundaryTheta_eq hasIndependentTangentSums_thetaH
    (hemiBranching pt0_mem_hemi isOpen_univ (mem_univ pt0)).toLocalBranchingStructure
    (mem_univ pt0)]
  have h : pt0 ∈ Ph.submanifoldBoundary (hemi ∩ univ) := by
    rw [inter_univ]
    exact mem_submanifoldBoundary_hemi pt0_mem_hemi pt0_mem_equator.2
  change ∑ i ∈ Finset.univ.filter fun (_ : Unit) =>
    pt0 ∈ Ph.submanifoldBoundary (hemi ∩ univ), (1 : ℚ) = 1
  rw [Finset.filter_true_of_mem fun _ _ => h]
  simp

theorem e8w_boundary_nonempty : (supp (AH.X.boundaryTheta thetaH)).Nonempty :=
  ⟨pt0, by change (0 : ℚ) < (trivial Ph).boundaryTheta thetaH pt0; rw [boundaryTheta_pt0]; norm_num⟩

theorem e8w_supp_nonempty : (supp thetaH).Nonempty := ⟨pt0, by rw [supp_thetaH]; exact pt0_mem_hemi⟩

/-! ### Hypothesis 1: partitions of unity -/

/-- **`[0, ∞) × ℝ²` admits sc-smooth partitions of unity** (Theorem 5.5.10 with the chart `id`,
whose model has the approximation property by Proposition 5.5.11). -/
theorem Ph_admitsScPartitionsOfUnity : Ph.AdmitsScPartitionsOfUnity := by
  refine theorem_5_5_10.2 ⟨{chartQ}, fun φ hφ => ?_, fun x => ⟨chartQ, mem_singleton _,
    mem_univ x⟩, fun φ hφ => ?_⟩
  · rw [mem_singleton_iff.1 hφ]; exact isChart_chartQ
  · rw [mem_singleton_iff.1 hφ]
    exact proposition_5_5_11 _ (admitsContDiffPartitionsOfUnity_of_finiteDimensional V3)

theorem e8w_hasScPartitionsOfUnity : AH.X.HasScPartitionsOfUnity :=
  hasScPartitionsOfUnity_trivial Ph Ph_admitsScPartitionsOfUnity

theorem e8w_isBranchedEpSubgroupoid : AH.X.IsBranchedEpSubgroupoid thetaH :=
  isBranchedEpSubgroupoid_thetaH

theorem e8w_isCompactBranched : AH.X.IsCompactBranched thetaH := isCompactBranched_thetaH

theorem e8w_isOrientation : AH.X.IsOrientation thetaH TH := isOrientation_thetaH

/-- **The hypotheses of Theorems 9.5.17 and 9.5.18 (Stokes), 2021 pp. 449–450, with `m = 1`,
nonempty support and nonempty boundary**: for `X = [0, ∞) × ℝ²` (trivial ep-groupoid),
`Θ = 1_{hemi}` and `T̂ = T(hemi, o)`. -/
theorem e8w_stokes_hypotheses :
    AH.X.HasScPartitionsOfUnity ∧ AH.X.IsBranchedEpSubgroupoid thetaH ∧
      AH.X.IsCompactBranched thetaH ∧ AH.X.IsOrientation thetaH TH ∧
      (∀ x ∈ supp thetaH, ∃ C : AH.X.OrientedTameStructure 2 thetaH x,
        C.Represents TH ∧ (∀ i, C.M i ∈ (AH.epFormsInftyEval 2).sheets) ∧
          ∀ i, (C.boundarySheet i).Nonempty →
            C.boundarySheet i ∈ (AH.epFormsInftyEval 1).msheets) ∧
      (supp (AH.X.boundaryTheta thetaH)).Nonempty ∧ (supp thetaH).Nonempty :=
  ⟨e8w_hasScPartitionsOfUnity, e8w_isBranchedEpSubgroupoid, e8w_isCompactBranched,
    e8w_isOrientation, e8w_hcov, e8w_boundary_nonempty, e8w_supp_nonempty⟩

end E8W

end Polyfold
