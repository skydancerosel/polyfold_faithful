import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_113

set_option maxSynthPendingDepth 3

/-! Round trip for V17_113 (2021 Theorem 17.6.7 and (17.90), p. 823: Stokes for oriented
branched ep⁺-subcategories of a polyfold).

Universes at `0` (`GCT.{0}`, models in `EP.{0}`; the half-plane example is universe-free).

**Harness.**  The statement of `halfPlaneArc_stokes` contains the proof term
`halfPlaneArc_isTameOriented` (an item theorem), so every term whose type mentions `A` reaches it
(not a `_proof_` field, so `#rt_check_soft` reports it too).  `A'` is `A` with that conjunct
restated with the copy `halfPlaneArc_isTameOriented'`; `A = A'` by `rfl` (proof irrelevance), and
`A_to_B`, `B_to_A` are point-free transports of `A'_to_B`, `B_to_A'`. -/

namespace RoundTrip.V17_113
open Polyfold
open Polyfold.GCT.PolyfoldConstruction
open Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory
open Polyfold.EpGroupoid Polyfold.EPLocalization Polyfold.EPLocalization.EPLoc Polyfold.HalfCircle

def A : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_all.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_all.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_book_all.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_book_all.{0}) ∧
  (type_of% @Polyfold.EP.stokesWithoutPartitions_all.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_of_epStokes.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_hyp.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_of_epStokes.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_hyp.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_of_epStokes_of_family.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_book.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_book_hyp.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_book.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_properties) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_isTameOriented) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_boundaryVia_eq_one) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.halfPlaneModel_hasScPartitionsOfUnity) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_stokes)

set_option maxHeartbeats 2000000 in
theorem A_holds : A :=
  ⟨@Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_all.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_all.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_book_all.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_book_all.{0},
    @Polyfold.EP.stokesWithoutPartitions_all.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_of_epStokes.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_hyp.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_of_epStokes.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_hyp.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_of_epStokes_of_family.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_book.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_book_hyp.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_book.{0},
    @Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_properties,
    @Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_isTameOriented,
    @Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_boundaryVia_eq_one,
    @Polyfold.GCT.PolyfoldConstruction.halfPlaneModel_hasScPartitionsOfUnity,
    @Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_stokes⟩

/-! Re-proofs (copies of the project's proofs, from non-item lemmas) of the conjuncts that are not
statements about `C`-level Stokes: ep-level Stokes for every ep-groupoid (from Chapter 9's
`theorem_9_5_17_all`, `theorem_9_5_18_all` and their `n = 1` forms), and the facts about the
half-plane example. -/

theorem stokesWithoutPartitions_all' (X : EP.{0}) : X.StokesWithoutPartitions where
  stokes hm _ _ hΘ hcpt hT hloc ω := X.theorem_9_5_17_all hm hΘ hcpt hT hloc ω
  stokesEff hm hLUC _ _ hΘ hcpt hT hloc ω := X.theorem_9_5_18_all hm hLUC hΘ hcpt hT hloc ω
  stokesDim1 hΘ hcpt hT hloc ω := X.theorem_9_5_17_dim1_all hΘ hcpt hT hloc ω
  stokesEffDim1 hΘ hcpt hT hloc ω := X.theorem_9_5_18_dim1_all hΘ hcpt hT hloc ω

theorem halfPlaneArc_isTameOriented' : halfPlaneArc.IsTameOriented (0 + 1) :=
  ⟨halfPlaneFamily, halfPlaneArc_isTameOrientedVia halfPlaneFamily⟩

theorem halfPlaneArc_boundaryVia_eq_one' (c : halfPlaneConstruction.CoveringFamily) :
    halfPlaneArc.boundaryVia c ((halfPlaneConstruction.modelFunctor halfPlaneFamily.Ψ).obj
      (halfPlaneModelFunctor.obj HalfCircle.pt1)) = 1 := by
  rw [← halfPlaneArc.definition_17_6_5 halfPlaneFamily c]
  have h := congrFun (halfPlaneArc.modelPull_boundaryVia halfPlaneFamily)
    (halfPlaneModelFunctor.obj HalfCircle.pt1)
  refine h.trans ?_
  change (halfPlaneConstruction.modelEP halfPlaneFamily.Ψ).X.boundaryTheta
      (halfPlaneConstruction.modelPull halfPlaneFamily.Ψ halfPlaneTheta)
      (halfPlaneModelFunctor.obj HalfCircle.pt1) = 1
  rw [modelPull_halfPlaneTheta, halfPlaneModelTheta,
    ← EpFunctor.boundaryTheta_pushforwardTheta isEquivalence_halfPlaneModelFunctor
      isBranchedEpSubgroupoid_thetaA hasIndependentTangentSums_thetaA]
  change halfPlaneModelFunctor.pullbackTheta
      (halfPlaneModelFunctor.pushforwardTheta (AA.X.boundaryTheta thetaA)) HalfCircle.pt1 = 1
  rw [EpFunctor.pullbackTheta_pushforwardTheta isEquivalence_halfPlaneModelFunctor.full
    (AA.X.isFunctorial_boundaryTheta isBranchedEpSubgroupoid_thetaA
      hasIndependentTangentSums_thetaA)]
  exact boundaryTheta_pt1

theorem halfPlaneModel_hasScPartitionsOfUnity' :
    (halfPlaneConstruction.modelEP halfPlaneFamily.Ψ).X.HasScPartitionsOfUnity := by
  refine EpGroupoid.theorem_7_5_7 _ ?_ ?_
  · have := metrizableSpace_modelOrbitSpace_of_family (S := halfPlaneConstruction)
      (Ψ := halfPlaneFamily.Ψ)
    let _ := TopologicalSpace.metrizableSpaceMetric
      (halfPlaneConstruction.modelEP halfPlaneFamily.Ψ).X.OrbitSpace
    exact (inferInstance :
      ParacompactSpace (halfPlaneConstruction.modelEP halfPlaneFamily.Ψ).X.OrbitSpace)
  · refine theorem_5_5_10.2 ⟨{MPolyfold.sigmaChart PUnit.unit chartA}, fun φ hφ => ?_,
      fun x => ⟨_, Set.mem_singleton _, ?_⟩, fun φ hφ => ?_⟩
    · rw [Set.mem_singleton_iff.1 hφ]; exact MPolyfold.IsChart.sigmaChart isChart_chartA
    · obtain ⟨i, y⟩ := x
      exact ⟨y, Set.mem_univ y, rfl⟩
    · rw [Set.mem_singleton_iff.1 hφ]
      exact proposition_5_5_11 _ (admitsContDiffPartitionsOfUnity_of_finiteDimensional V2)

theorem halfPlaneArc_properties' :
    (∃ α, 0 < halfPlaneArc.Θ α) ∧
      (GCT.translation (Multiplicative (ZMod 1)) Q2
        isScSmoothMap_z1_smul_halfPlane).IsCompactBranched halfPlaneArc.Θ ∧
      (∀ c, halfPlaneArc.IsTameOrientedVia c (0 + 1)) ∧
      (∀ c, ∃ α, halfPlaneArc.boundaryVia c α = 1) ∧
      halfPlaneConstruction.IsLUC ∧
      (halfPlaneConstruction.modelEP halfPlaneFamily.Ψ).X.HasScPartitionsOfUnity := by
  refine ⟨?_, isCompactBranched_halfPlaneTheta, halfPlaneArc_isTameOrientedVia,
    fun c => ⟨_, halfPlaneArc_boundaryVia_eq_one' c⟩, halfPlane_isLUC,
    halfPlaneModel_hasScPartitionsOfUnity'⟩
  obtain ⟨x, hx⟩ := supp_halfPlaneModelTheta_nonempty
  refine ⟨(halfPlaneConstruction.modelFunctor halfPlaneFamily.Ψ).obj x, ?_⟩
  have h := congrFun modelPull_halfPlaneTheta x
  change 0 < halfPlaneConstruction.modelPull halfPlaneFamily.Ψ halfPlaneTheta x
  rw [h]
  exact hx

/-- `halfPlaneArc_stokes` with the copy `halfPlaneArc_isTameOriented'` in its statement. -/
def StokesHP' : Prop :=
  ∀ ω : halfPlaneConstruction.catFormsInfty 0,
    halfPlaneArc.integral (Nat.succ_pos 0) isCompactBranched_halfPlaneTheta
        halfPlaneArc_isTameOriented' (halfPlaneConstruction.catFormsInftyD 0 ω) =
      halfPlaneArc.boundaryIntegralDim1 isCompactBranched_halfPlaneTheta
        halfPlaneArc_isTameOriented' ω

set_option maxHeartbeats 2000000 in
/-- `B` (case `n = 1`) gives Stokes for the half-plane example (`integral` is the integral on the
covering family chosen by the tameness proof). -/
theorem stokesHP'_of_B (hB : B) : StokesHP' := by
  intro ω
  have key := (hB _ halfPlaneConstruction halfPlaneArc isCompactBranched_halfPlaneTheta).2
    halfPlaneArc_isTameOriented'.choose halfPlaneArc_isTameOriented'.choose_spec ω
  exact key

def A' : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_all.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_all.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_book_all.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_book_all.{0}) ∧
  (type_of% @Polyfold.EP.stokesWithoutPartitions_all.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_of_epStokes.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_hyp.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_of_epStokes.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_hyp.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_of_epStokes_of_family.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_book.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_book_hyp.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_book.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_properties) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_isTameOriented) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_boundaryVia_eq_one) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.halfPlaneModel_hasScPartitionsOfUnity) ∧
  StokesHP'

theorem A_eq_A' : A = A' := rfl

theorem A'_to_B : A' → B := by
  rintro ⟨h1, h2, -⟩ C S A hc
  exact ⟨fun m hm c ht ω => h1 A c hm hc ht ω, fun c ht ω => h2 A c hc ht ω⟩

theorem B_to_A' : B → A' := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- theorem_17_6_7_all, theorem_17_6_7_dim1_all
  · intro C S m A c hm hc ht ω; exact (hB C S A hc).1 m hm c ht ω
  · intro C S A c hc ht ω; exact (hB C S A hc).2 c ht ω
  -- theorem_17_6_7_book_all, theorem_17_6_7_dim1_book_all (`integral` is the integral at `h.choose`)
  · intro C S m A _ hm hc h ω; exact (hB C S A hc).1 m hm h.choose h.choose_spec ω
  · intro C S A _ hc h ω; exact (hB C S A hc).2 h.choose h.choose_spec ω
  -- EP.stokesWithoutPartitions_all (re-proved outright)
  · exact stokesWithoutPartitions_all'
  -- the forms with an extra hypothesis on the model
  · intro C S m A c _ hm hc ht ω; exact (hB C S A hc).1 m hm c ht ω
  · intro C S m A c _ hm hc ht ω; exact (hB C S A hc).1 m hm c ht ω
  · intro C S A c _ hc ht ω; exact (hB C S A hc).2 c ht ω
  · intro C S A c _ hc ht ω; exact (hB C S A hc).2 c ht ω
  · intro C S m A c₀ c _ hm hc _ ht ω; exact (hB C S A hc).1 m hm c ht ω
  · intro C S m A _ _ hm hc h ω; exact (hB C S A hc).1 m hm h.choose h.choose_spec ω
  · intro C S m A _ _ hm hc h ω; exact (hB C S A hc).1 m hm h.choose h.choose_spec ω
  · intro C S A _ _ hc h ω; exact (hB C S A hc).2 h.choose h.choose_spec ω
  -- the half-plane example: properties re-proved, Stokes from `B`
  · exact halfPlaneArc_properties'
  · exact halfPlaneArc_isTameOriented'
  · exact halfPlaneArc_boundaryVia_eq_one'
  · exact halfPlaneModel_hasScPartitionsOfUnity'
  · exact stokesHP'_of_B hB

theorem A_to_B : A → B := A'_to_B
theorem B_to_A : B → A := B_to_A'

/-- Main conjuncts: `theorem_17_6_7_all ∧ theorem_17_6_7_dim1_all` (Stokes on the model of every
covering family, the two cases; `B` is their conjunction). -/
def Main : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_all.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_all.{0})

theorem main_to_B : Main → B := by
  rintro ⟨h1, h2⟩ C S A hc
  exact ⟨fun m hm c ht ω => h1 A c hm hc ht ω, fun c ht ω => h2 A c hc ht ω⟩

theorem B_to_main : B → Main := fun hB => ⟨(B_to_A' hB).1, (B_to_A' hB).2.1⟩

#rt_check RoundTrip.V17_113.A_to_B [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_all, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_all, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_book_all, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_book_all, Polyfold.EP.stokesWithoutPartitions_all, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_of_epStokes, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_hyp, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_of_epStokes, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_hyp, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_of_epStokes_of_family, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_book, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_book_hyp, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_book, Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_properties, Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_isTameOriented, Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_boundaryVia_eq_one, Polyfold.GCT.PolyfoldConstruction.halfPlaneModel_hasScPartitionsOfUnity, Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_stokes]
#rt_check RoundTrip.V17_113.B_to_A [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_all, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_all, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_book_all, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_book_all, Polyfold.EP.stokesWithoutPartitions_all, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_of_epStokes, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_hyp, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_of_epStokes, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_hyp, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_of_epStokes_of_family, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_book, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_book_hyp, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_book, Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_properties, Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_isTameOriented, Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_boundaryVia_eq_one, Polyfold.GCT.PolyfoldConstruction.halfPlaneModel_hasScPartitionsOfUnity, Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_stokes]
#rt_check RoundTrip.V17_113.main_to_B [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_all, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_all, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_book_all, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_book_all, Polyfold.EP.stokesWithoutPartitions_all, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_of_epStokes, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_hyp, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_of_epStokes, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_hyp, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_of_epStokes_of_family, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_book, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_book_hyp, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_book, Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_properties, Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_isTameOriented, Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_boundaryVia_eq_one, Polyfold.GCT.PolyfoldConstruction.halfPlaneModel_hasScPartitionsOfUnity, Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_stokes]
#rt_check RoundTrip.V17_113.B_to_main [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_all, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_all, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_book_all, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_book_all, Polyfold.EP.stokesWithoutPartitions_all, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_of_epStokes, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_hyp, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_of_epStokes, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_hyp, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_of_epStokes_of_family, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_book, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_book_hyp, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_book, Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_properties, Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_isTameOriented, Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_boundaryVia_eq_one, Polyfold.GCT.PolyfoldConstruction.halfPlaneModel_hasScPartitionsOfUnity, Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_stokes]
#rt_overlap RoundTrip.V17_113.B_to_A [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_all, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_all, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_book_all, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_book_all, Polyfold.EP.stokesWithoutPartitions_all, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_of_epStokes, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_hyp, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_of_epStokes, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_hyp, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_of_epStokes_of_family, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_book, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_book_hyp, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_dim1_book, Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_properties, Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_isTameOriented, Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_boundaryVia_eq_one, Polyfold.GCT.PolyfoldConstruction.halfPlaneModel_hasScPartitionsOfUnity, Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_stokes]

end RoundTrip.V17_113
