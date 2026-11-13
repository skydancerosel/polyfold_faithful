import Polyfold.Chapter9.GapP3_K2_Arc
import Polyfold.Chapter9.GapP3_K2_AllStructuresDim1
import Polyfold.Chapter9.GapP3_K2_HemisphereEff

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, **Theorems 9.5.17 and 9.5.18 (Stokes) for `n = 1`** (pp. 449–450), gap
G.110: a witness with nonempty boundary.  Numbers and pages are the 2021 text's.

# A compact oriented `1`-dimensional witness with boundary

`X` is the trivial ep-groupoid of the half-plane `[0, ∞) × ℝ` (`Pa`, `GapP3_K2_Arc`), packaged as
the object `AA` of `EP`, and `Θ = 1_{arc}` (`thetaA`) for the closed right half-circle `arc`,
oriented by the frame `f(a)` (`arcOrientation`), with `T̂(y) = T_y(arc, o)` on `arc` (`TA`).
This is E8W's hemisphere witness one dimension lower.  Then:

* `arc_hasScPartitionsOfUnity`, `arc_isBranchedEpSubgroupoid`, `arc_isCompactBranched`,
  `arc_isOrientation`, `arc_isLUC`;
* `arc_hloc`: every point of `supp Θ = arc` has an oriented tame structure of dimension `1`
  describing `T̂` (the text's "oriented, tame");
* `arc_boundary_nonempty`: `∂Θ(pt1) = 1` at the end point `pt1 = (0, 1)`;
* **`K2Arc.k2_arc_stokes`**: `supp(∂Θ) ≠ ∅` and `∫_Θ̂ dω = μ^{∂Θ̂}_ω(∂S)` for every
  `ω ∈ Ω⁰_{ep,∞}(X)` (`EP.theorem_9_5_17_dim1`);
* **`K2Arc.k2_arc_stokes_eff`**: the same for Theorem 9.5.18 (`EP.theorem_9_5_18_dim1_isLUC`);
* `K2Arc.k2_arc_boundaryMeasure`: the measure has the local formula of Theorem 9.5.15 for every
  oriented tame structure (`EP.boundaryBranchedMeasureDim1_apply_all`).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology Module Submodule

noncomputable section

namespace Polyfold

open MPolyfold EpGroupoid

namespace K2Arc

/-! ### The orientation of the half-circle -/

theorem levelLift_chartA (z : Q2) : levelLift chartA 1 z = lev1 z.1 :=
  (bijective_toBase_E2 1).1 ((Pa.toBase_levelLift isChart_chartA (mem_univ z)
    (Pa_mem_levelSet 1 z)).trans (toBase_lev1 z.1).symm)

/-- **The tangent line of `arc`**: in the chart `id`, the chart vectors of `T_z arc` form
`z^⊥`. -/
theorem chartVec_image_arc {z : Q2} (hz : z ∈ arc) :
    chartVec isChart_chartA '' Pa.submanifoldTangent arc z =
      (LinearMap.ker (ell z.1 : V2 →ₗ[ℝ] ℝ) : Set V2) := by
  rw [chartVec_image_submanifoldTangent isChart_chartA arcData hz (arc_subset_Va hz)
    (mem_univ z), levelLift_chartA]
  erw [chartA_image_shrink, tangentSpace_arc ⟨hz, z.2⟩]

theorem one_add_pos_of_mem (z : Q2) : 0 < 1 + z.1.1 0 := by
  have : 0 ≤ z.1.1 0 := z.2 0
  linarith

theorem linearIndependent_frameVecQ (z : Q2) : LinearIndependent ℝ (frameVec z.1) :=
  linearIndependent_frameVec z.1

/-- The line spanned by the frame `f(z)`. -/
def arcN (z : Q2) : Submodule ℝ V2 := span ℝ (range (frameVec z.1))

theorem arcN_eq {z : Q2} (hz : z ∈ arc) :
    arcN z = LinearMap.ker (ell z.1 : V2 →ₗ[ℝ] ℝ) := by
  refine Submodule.eq_of_le_of_finrank_eq (span_le.2 (range_subset_iff.2 fun i => ?_)) ?_
  · change ell z.1 (frameVec z.1 i) = 0
    rw [ell_apply]
    exact ell_frameVec hz (one_add_pos_of_mem z) i
  · rw [arcN, finrank_span_eq_card (linearIndependent_frameVecQ z), finrank_ker_ell hz,
      Fintype.card_fin]

/-- The frames of `T_z arc` positive for the orientation given by `f(z)`. -/
def arcFrames (z : Q2) : Set (Fin 1 → Pa.TangentSpace) :=
  {v | (∀ i, v i ∈ Pa.submanifoldTangent arc z) ∧ ∃ b : Basis (Fin 1) ℝ (arcN z),
    (∀ i, (b i : V2) = chartVec isChart_chartA (v i)) ∧
      b.orientation = (Basis.span (linearIndependent_frameVecQ z)).orientation}

theorem isChartOrientation_arc {z : Q2} (hz : z ∈ arc) :
    IsChartOrientation isChart_chartA ⟨1, Pa.submanifoldTangent arc z, arcFrames z⟩ := by
  refine ⟨arcN z, ?_, FiniteDimensional.span_of_finite ℝ (finite_range _), ?_,
    (Basis.span (linearIndependent_frameVecQ z)).orientation, rfl⟩
  · change ((arcN z : Set V2)) = _
    rw [chartVec_image_arc hz, arcN_eq hz]
  · change finrank ℝ (arcN z) = 1
    rw [arcN, finrank_span_eq_card (linearIndependent_frameVecQ z), Fintype.card_fin]

theorem continuousOn_frameVecQ :
    ContinuousOn (fun (z : Q2) (i : Fin 1) => frameVec z.1 i) univ := by
  refine continuousOn_pi.2 fun i => ?_
  have h := continuousOn_frameVec i
  refine (h.comp continuous_subtype_val.continuousOn fun z _ => ?_)
  exact one_add_pos_of_mem z

/-- **An orientation of the half-circle** (Definition 9.3.3): positive frames those whose chart
vector is a positive multiple of `f(z)`. -/
def arcOrientation : Pa.SubmanifoldOrientation arc 1 where
  frames := arcFrames
  isOrientedAt _ hz := ⟨fun _ hα => hα.1, chartA, isChart_chartA, mem_univ _,
    isChartOrientation_arc hz⟩
  continuous _ z hz := by
    have hlift : ∀ z' ∈ arc, ∀ i : Fin 1, ∃ α ∈ Pa.submanifoldTangent arc z',
        chartVec isChart_chartA α = frameVec z'.1 i := fun z' hz' i => by
      have : frameVec z'.1 i ∈ chartVec isChart_chartA '' Pa.submanifoldTangent arc z' := by
        rw [chartVec_image_arc hz', ← arcN_eq hz']
        exact subset_span (mem_range_self i)
      exact this
    obtain ⟨α₀, -, -⟩ := hlift z hz 0
    have : Nonempty Pa.TangentSpace := ⟨α₀⟩
    choose! e he1 he2 using hlift
    refine ⟨chartA, isChart_chartA, univ, isOpen_univ, mem_univ z, subset_univ _,
      fun z' i => e z' i, fun z' hz' => ⟨fun i => he1 z' hz'.1 i,
        Basis.span (linearIndependent_frameVecQ z'), fun i => ?_, rfl⟩, ?_⟩
    · exact (congrArg Subtype.val (Basis.span_apply (linearIndependent_frameVecQ z') i)).trans
        (he2 z' hz'.1 i).symm
    · exact (continuousOn_frameVecQ.mono (subset_univ _)).congr fun z' hz' =>
        funext fun i => he2 z' hz'.1 i

/-! ### `Θ = 1_{arc}` and its oriented tangent sums -/

open scoped Classical in
/-- `Θ = 1_{arc}`. -/
def thetaA (y : Q2) : ℚ := if y ∈ arc then 1 else 0

open scoped Classical in
/-- `T̂(y) = T_y(arc, o)` for `y ∈ arc`, `0` otherwise. -/
def TA (y : Q2) : Pa.OrTangent →₀ ℚ :=
  if y ∈ arc then Finsupp.single (arcOrientation.tangent y) 1 else 0

theorem supp_thetaA : supp thetaA = arc := by
  ext y
  change 0 < thetaA y ↔ _
  by_cases hy : y ∈ arc <;> simp [thetaA, hy]

/-- **The oriented local branching structure of `Θ` at `x ∈ arc`** on an open `W ∋ x`: the one
sheet `arc ∩ W`, weight `1`, the restricted orientation. -/
def arcBranching {x : Q2} (hx : x ∈ arc) {W : Set Q2} (hW : IsOpen W) (hxW : x ∈ W) :
    (trivial Pa).OrientedBranchingStructure thetaA x where
  U := W
  isOpen_U := hW
  mem_U := hxW
  ι := Unit
  M _ := arc ∩ W
  subset_U _ := inter_subset_right
  isSmoothSubmanifold _ := isSmoothSubmanifold_arc.inter_isOpen hW
  mem_M _ := ⟨hx, hxW⟩
  isProperMap _ := by
    refine (isProperMap_inclusion_iff _).2 ?_
    convert isClosed_arc.preimage continuous_subtype_val using 1
    ext y
    exact ⟨fun h => h.1, fun h => ⟨h, y.2⟩⟩
  σ _ := 1
  σ_pos _ := one_pos
  eq_sum y hy := by
    by_cases h : y ∈ arc
    · simp [thetaA, h, hy]
    · simp [thetaA, h]
  dim _ := 1
  isSubmanifoldOfDim _ := isSubmanifoldOfDim_arc.inter_isOpen hW
  orient _ := arcOrientation.restrict hW

theorem arcBranching_orientedSum {x : Q2} (hx : x ∈ arc) {W : Set Q2} (hW : IsOpen W)
    (hxW : x ∈ W) {y : Q2} (hy : y ∈ W) : (arcBranching hx hW hxW).orientedSum y = TA y := by
  have : Unique (arcBranching hx hW hxW).ι := inferInstanceAs (Unique Unit)
  rw [OrientedBranchingStructure.orientedSum, Finset.sum_filter, Fintype.sum_unique, TA]
  by_cases h : y ∈ arc
  · rw [if_pos (show y ∈ (arcBranching hx hW hxW).M default from ⟨h, hy⟩), if_pos h]
    exact congrArg (fun g => Finsupp.single g (1 : ℚ)) (arcOrientation.restrict_tangent hW hy)
  · rw [if_neg (show y ∉ (arcBranching hx hW hxW).M default from fun h' => h h'.1), if_neg h]
    rfl

theorem TA_mem_GrHat (y : Q2) : TA y ∈ (trivial Pa).GrHat y := by
  by_cases h : y ∈ arc
  · rw [← arcBranching_orientedSum h isOpen_univ (mem_univ y) (mem_univ y)]
    exact OrientedBranchingStructure.orientedSum_mem _ y
  · rw [TA, if_neg h]
    exact zero_mem_GrHat y

/-! ### Branched, compact, oriented -/

/-- **`Θ = 1_{arc}` is a branched ep⁺-subgroupoid** (Definition 9.1.2). -/
theorem isBranchedEpSubgroupoid_thetaA : (trivial Pa).IsBranchedEpSubgroupoid thetaA where
  nonneg y := by unfold thetaA; split_ifs <;> norm_num
  isFunctorial _ := rfl
  support_subset y _ := Pa_mem_smoothSet y
  paracompactSpace_orbitSupp :=
    paracompactSpace_orbitSupp_trivial_of_isClosed Pa (by rw [supp_thetaA]; exact isClosed_arc)
  localBranching x hx := by
    rw [supp_thetaA] at hx
    exact ⟨(arcBranching hx isOpen_univ (mem_univ x)).toLocalBranchingStructure⟩

/-- **`Θ` is compact** (Definition 9.1.6 (2)): `|supp Θ| = π(arc)`. -/
theorem isCompactBranched_thetaA : (trivial Pa).IsCompactBranched thetaA := by
  unfold IsCompactBranched orbitSupp
  rw [supp_thetaA]
  exact isCompact_arc.image (trivial Pa).continuous_π

theorem hasIndependentTangentSums_thetaA : (trivial Pa).HasIndependentTangentSums thetaA := by
  refine hasIndependentTangentSums_of_subset_goodSet fun y hy => ?_
  refine (mem_goodSet_iff isBranchedEpSubgroupoid_thetaA).2 ⟨hy, univ, univ_mem, fun z _ hz => ?_⟩
  rw [supp_thetaA] at hy hz
  simp [thetaA, hy, hz]

/-- **`T̂` is an orientation of `Θ`** (Definition 9.3.2). -/
theorem isOrientation_thetaA : (trivial Pa).IsOrientation thetaA TA :=
  IsOrientation.mk' hasIndependentTangentSums_thetaA (fun y _ => TA_mem_GrHat y)
    (fun φ _ => grHatPush_unit (TA_mem_GrHat φ))
    (fun y _ hy => by
      rw [supp_thetaA] at hy
      rw [TA, if_neg hy]
      rfl)
    fun x hx => by
      rw [supp_thetaA] at hx
      exact ⟨arcBranching hx isOpen_univ (mem_univ x), fun y hy _ =>
        (arcBranching_orientedSum hx isOpen_univ (mem_univ x) hy).symm⟩

/-! ### Oriented tame structures -/

/-- **The object `X = [0, ∞) × ℝ` (trivial ep-groupoid) of `EP`.** -/
abbrev AA : EP.{0} := EP.mk Q2 Q2 (trivial Pa)

/-- **The oriented tame structure at `x ∈ arc`** on the domain of a natural representation `R`. -/
def arcTame {x : Q2} (hx : x ∈ arc) (R : (trivial Pa).NaturalRep x) :
    (trivial Pa).OrientedTameStructure (0 + 1) thetaA x where
  toLocalBranchingStructure := (arcBranching hx R.isOpen_U R.mem_U).toLocalBranchingStructure
  rep := R
  U_eq := rfl
  hasPropernessProperty := hasPropernessProperty_trivial Pa R.isOpen_U
  hasTameInducedStructure _ :=
    HasTameInducedStructure.inter_isOpen isSmoothSubmanifold_arc hasTameInducedStructure_arc
      R.isOpen_U
  isSubmanifoldOfDim _ := isSubmanifoldOfDim_arc.inter_isOpen R.isOpen_U
  orient _ := arcOrientation.restrict R.isOpen_U

theorem arcTame_represents {x : Q2} (hx : x ∈ arc) (R : (trivial Pa).NaturalRep x) :
    (arcTame hx R).Represents TA := fun _ hy _ =>
  (arcBranching_orientedSum hx R.isOpen_U R.mem_U hy).symm

/-- **"Oriented, tame" for `Θ = 1_{arc}`**: an oriented tame structure of dimension `1`
describing `T̂` at every point of `supp Θ`. -/
theorem arc_hloc : ∀ x ∈ supp thetaA, ∃ C : AA.X.OrientedTameStructure (0 + 1) thetaA x,
    C.Represents TA := by
  intro x hx
  rw [supp_thetaA] at hx
  obtain ⟨R, -⟩ := theorem_7_1_13 (trivial Pa) x isOpen_univ (mem_univ x)
  exact ⟨arcTame hx R, arcTame_represents hx R⟩

/-! ### Nontriviality -/

theorem pt1_mem_arc : pt1 ∈ arc := pt1_mem_arcEnds.1

/-- **`∂Θ(pt1) = 1`** at the end point `pt1 = (0, 1)`. -/
theorem boundaryTheta_pt1 : (trivial Pa).boundaryTheta thetaA pt1 = 1 := by
  classical
  rw [boundaryTheta_eq hasIndependentTangentSums_thetaA
    (arcBranching pt1_mem_arc isOpen_univ (mem_univ pt1)).toLocalBranchingStructure
    (mem_univ pt1)]
  have h : pt1 ∈ Pa.submanifoldBoundary (arc ∩ univ) := by
    rw [inter_univ]
    exact mem_submanifoldBoundary_arc pt1_mem_arc pt1_mem_arcEnds.2
  change ∑ i ∈ Finset.univ.filter fun (_ : Unit) =>
    pt1 ∈ Pa.submanifoldBoundary (arc ∩ univ), (1 : ℚ) = 1
  rw [Finset.filter_true_of_mem fun _ _ => h]
  simp

theorem arc_boundary_nonempty : (supp (AA.X.boundaryTheta thetaA)).Nonempty :=
  ⟨pt1, by change (0 : ℚ) < (trivial Pa).boundaryTheta thetaA pt1; rw [boundaryTheta_pt1]; norm_num⟩

theorem arc_supp_nonempty : (supp thetaA).Nonempty := ⟨pt1, by rw [supp_thetaA]; exact pt1_mem_arc⟩

/-! ### Partitions of unity, LUC -/

/-- **`[0, ∞) × ℝ` admits sc-smooth partitions of unity** (Theorem 5.5.10 with the chart `id`,
Proposition 5.5.11). -/
theorem Pa_admitsScPartitionsOfUnity : Pa.AdmitsScPartitionsOfUnity := by
  refine theorem_5_5_10.2 ⟨{chartA}, fun φ hφ => ?_, fun x => ⟨chartA, mem_singleton _,
    mem_univ x⟩, fun φ hφ => ?_⟩
  · rw [mem_singleton_iff.1 hφ]; exact isChart_chartA
  · rw [mem_singleton_iff.1 hφ]
    exact proposition_5_5_11 _ (admitsContDiffPartitionsOfUnity_of_finiteDimensional V2)

theorem arc_hasScPartitionsOfUnity : AA.X.HasScPartitionsOfUnity :=
  hasScPartitionsOfUnity_trivial Pa Pa_admitsScPartitionsOfUnity

theorem arc_isBranchedEpSubgroupoid : AA.X.IsBranchedEpSubgroupoid thetaA :=
  isBranchedEpSubgroupoid_thetaA

theorem arc_isCompactBranched : AA.X.IsCompactBranched thetaA := isCompactBranched_thetaA

theorem arc_isOrientation : AA.X.IsOrientation thetaA TA := isOrientation_thetaA

/-- The trivial ep-groupoid of the half-plane has the local unique continuation property
(Definition 7.2.18). -/
theorem arc_isLUC : AA.X.IsLUC :=
  AA.X.isLUC_iff_forall_naturalRep.2 fun _ R => E8W.hasLUC_trivial R

/-! ### Stokes for the half-circle -/

/-- **Theorem 9.5.17 for `n = 1`, for the closed half-circle**: `supp(∂Θ) ≠ ∅` (the end points)
and `∫_Θ̂ dω = μ^{∂Θ̂}_ω(∂S)` for every `ω ∈ Ω⁰_{ep,∞}(X)`, with the boundary measure of Theorem
9.5.15 for `n = 1`. -/
theorem k2_arc_stokes :
    (supp (AA.X.boundaryTheta thetaA)).Nonempty ∧
    ∀ ω : AA.epFormsInfty 0,
      (AA.epFormsInftyEval (0 + 1)).tameBranchedIntegral (Nat.succ_pos 0)
          arc_isBranchedEpSubgroupoid arc_isCompactBranched arc_isOrientation arc_hloc
          (AA.epFormsInftyD 0 ω) =
        AA.boundaryBranchedMeasureDim1 arc_isBranchedEpSubgroupoid arc_isCompactBranched
          arc_isOrientation arc_hloc ω univ :=
  ⟨arc_boundary_nonempty, AA.theorem_9_5_17_dim1 arc_hasScPartitionsOfUnity
    arc_isBranchedEpSubgroupoid arc_isCompactBranched arc_isOrientation arc_hloc⟩

/-- **Theorem 9.5.18 for `n = 1`, for the closed half-circle**: `X` has LUC, `supp(∂Θ) ≠ ∅`, and
`∮_Θ̂ dω = μ^{∂Θ̂,eff}_ω(∂S)` for every `ω ∈ Ω⁰_{ep,∞}(X)`. -/
theorem k2_arc_stokes_eff :
    AA.X.IsLUC ∧ (supp (AA.X.boundaryTheta thetaA)).Nonempty ∧
    ∀ ω : AA.epFormsInfty 0,
      (AA.epFormsInftyEval (0 + 1)).tameBranchedIntegralEff (Nat.succ_pos 0)
          arc_isBranchedEpSubgroupoid arc_isCompactBranched arc_isOrientation
          (AA.hloc_hasLUC_dim1 arc_isLUC arc_hloc) (AA.epFormsInftyD 0 ω) =
        AA.boundaryBranchedMeasureEffDim1 arc_isBranchedEpSubgroupoid arc_isCompactBranched
          arc_isOrientation (AA.hloc_hasLUC_dim1 arc_isLUC arc_hloc) ω univ :=
  ⟨arc_isLUC, arc_boundary_nonempty, AA.theorem_9_5_18_dim1_isLUC arc_hasScPartitionsOfUnity
    arc_isLUC arc_isBranchedEpSubgroupoid arc_isCompactBranched arc_isOrientation arc_hloc⟩

/-- **The hypotheses of Theorems 9.5.15–9.5.18 for `n = 1` hold jointly with `supp Θ ≠ ∅` and
`supp(∂Θ) ≠ ∅`.** -/
theorem k2_arc_hypotheses :
    AA.X.HasScPartitionsOfUnity ∧ AA.X.IsLUC ∧ AA.X.IsBranchedEpSubgroupoid thetaA ∧
      AA.X.IsCompactBranched thetaA ∧ AA.X.IsOrientation thetaA TA ∧
      (∀ x ∈ supp thetaA, ∃ C : AA.X.OrientedTameStructure (0 + 1) thetaA x,
        C.Represents TA) ∧
      (supp (AA.X.boundaryTheta thetaA)).Nonempty ∧ (supp thetaA).Nonempty :=
  ⟨arc_hasScPartitionsOfUnity, arc_isLUC, arc_isBranchedEpSubgroupoid, arc_isCompactBranched,
    arc_isOrientation, arc_hloc, arc_boundary_nonempty, arc_supp_nonempty⟩

end K2Arc

end Polyfold
