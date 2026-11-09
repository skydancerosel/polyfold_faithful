import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_62

/-! Round trip for V9_62 (2021 Proposition 9.6.5, p. 456, and the formula on p. 457).

The item lists the definition `LocalBranchingStructure.IsTopSlice` (vocabulary: a finite set `S`
of points of `U` off the lower-dimensional sheets, meeting each top sheet with tangent `T` exactly
once and missing the top sheets with other tangents) and five theorems; `A` is the conjunction of
their types, universes at `0`: `proposition_9_6_5` (`A1`: under the graph representation at `x`,
`HasGraphChartAt x`, every open `W ∋ x` contains a top slice for the class of `i₀`, at every `x`,
for every `Θ`), `sum_class_eq_sum_of_isTopSlice` (`A2`: the class weight is `∑_{y ∈ S} Θ(y)`),
`dimPart_topDim_eq_sum_slices` (`A3`: the formula of p. 457 in slice form), and
`sum_class_eq_of_hasGraphChartAt`, `dimPart_topDim_eq_of_hasGraphChartAt` (`A4`, `A5`: the class
weights and `Θ_k(x)` do not depend on the structure, under `HasGraphChartAt x`).

`B` (as printed): at a top-bad `x` of a labelled structure of a branched `Θ`, (i) for every
tangent class `Ξ` there are blocks `I¹, …, I^p` partitioning **`I_k`** (the printed
`I_k = I¹ ⊔ ⋯ ⊔ I^p`), indices `i_e ∈ I^e` and sequences of top-good points `x^e_j → x` with
`x^e_j ∈ Mᵢ ↔ i ∈ I^e`; (ii) for any such data for all classes, `Θ_k(x) = ∑_Ξ ∑_e Θ_k(x^e_j)`.

* **`not_B`: `B` is false**, as its author predicted.  With the blocks partitioning `I_k`, each
  inner sum `∑_e Θ_k(x^e_j)` is `∑_{i ∈ I_k} σᵢ = Θ_k(x)` (`sum_dimPartB_of_isSliceDataB`), so
  (i)+(ii) give `Θ_k(x) = ♯(classes) · Θ_k(x)`, impossible as soon as there are two tangent
  classes.  Counterexample: the trivial ep-groupoid of `ℝ²`, `Θ = 1_{y=0} + 1_{y=x}` (the
  project's `isBranchedEpSubgroupoid_sum_rn`, `localBranchingStructure_sum_rn`), `x = 0`: top-bad,
  two classes (tangent lines `ℝ(1,0) ≠ ℝ(1,1)`, from the project's `chartVec_image_graph2'`); the
  data of (i) are taken from `B` itself.  Hence `A → B` is false (`not_A_to_B`).
* `B_to_A`: only ex falso from `not_B` (vacuous for the audit).
* Against the intended reading `BIntended` (blocks partitioning `Ξ`) no direction was attempted;
  the differences are listed in the JSON (slices vs. sequences of top-good points, the
  `HasGraphChartAt` hypothesis, top-bad vs. every `x`, branched `Θ`). -/

namespace RoundTrip.V9_62
open Polyfold EpGroupoid MPolyfold Set Submodule
open Classical

/-- The project's statement (universes at `0`). -/
def A1 : Prop := type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.proposition_9_6_5.{0}
def A2 : Prop :=
  type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.sum_class_eq_sum_of_isTopSlice.{0}
def A3 : Prop :=
  type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.dimPart_topDim_eq_sum_slices.{0}
def A4 : Prop :=
  type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.sum_class_eq_of_hasGraphChartAt.{0}
def A5 : Prop :=
  type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.dimPart_topDim_eq_of_hasGraphChartAt.{0}
def A : Prop := A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.LocalBranchingStructure.proposition_9_6_5.{0},
    @Polyfold.EpGroupoid.LocalBranchingStructure.sum_class_eq_sum_of_isTopSlice.{0},
    @Polyfold.EpGroupoid.LocalBranchingStructure.dimPart_topDim_eq_sum_slices.{0},
    @Polyfold.EpGroupoid.LocalBranchingStructure.sum_class_eq_of_hasGraphChartAt.{0},
    @Polyfold.EpGroupoid.LocalBranchingStructure.dimPart_topDim_eq_of_hasGraphChartAt.{0}⟩

/-! ### Glue (from `RoundTrip/Items/V9_2.lean`) -/

section Dim
variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {P : MPolyfold Z}

theorem tyMB_eq {A : Set Z} {y : Z} (hyA : y ∈ A) : TyMB P A y = P.submanifoldTangent A y := by
  ext α
  constructor
  · rintro ⟨d, hyV, β, hβ, rfl⟩
    have hβ' : P.levelVal 1 (P.tangentProj β) = y := hβ
    have hβV : β ∈ P.tangentPreimage d.V := by
      change P.levelVal 1 (P.tangentProj β) ∈ d.V
      rw [hβ']; exact hyV
    have := d.tmap_mem_submanifoldTangent hβV
    rwa [hβ', d.apply_eq_self ⟨hyA, hyV⟩] at this
  · rintro ⟨hαy, d, hyV, hfix⟩
    exact ⟨d, hyV, α, hαy, hfix⟩

theorem chartImgB_eq {φ : MChart Z} (hφ : P.IsChart φ) {A : Set Z} {y : Z} (hyA : y ∈ A) :
    chartImgB hφ (TyMB P A y) = P.chartTangent hφ A y := by
  rw [chartImgB, tyMB_eq hyA]
  rfl

theorem hasDimB_of {A : Set Z} (hA : P.IsSmoothSubmanifold A) {y : Z} {n : ℕ}
    (h : P.HasDimAt A y n) : HasDimB P A y n := by
  have hyA := h.1
  obtain ⟨φ, hφ, hyφ⟩ := P.exists_isChart_mem_source y
  obtain ⟨N, hN, hfin⟩ := exists_submodule_chartTangent hφ hA hyA hyφ
  refine ⟨φ, hφ, hyφ, N, hfin, ?_, ?_⟩
  · rw [chartImgB_eq hφ hyA, hN]
  · set d := hA.data hyA
    have hyV := hA.mem_data_V hyA
    have hy1 := d.mem_levelSet_one hyA hyV
    have hz := P.toBase_levelLift hφ hyφ hy1
    have h1 := h.finrank_eq d hφ hyV hyφ hz
    rw [← chartTangent_eq hφ d hyA hyV hyφ, ← hN, Submodule.span_eq] at h1
    exact h1

end Dim

/-! ### With the blocks partitioning `I_k`, each class contributes `Θ_k(x)` -/

section Gen
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {X : EpGroupoid Obj Mor} {Θ : Obj → ℚ} {x : Obj}

theorem sum_dimPartB_of_isSliceDataB (L : X.LocalBranchingStructure Θ x) (dim : L.ι → ℕ)
    {p : ℕ} {I : Fin p → Finset L.ι} {ie : Fin p → L.ι} {xs : Fin p → ℕ → Obj}
    (h : IsSliceDataB L dim (IkB L dim) p I ie xs) (j : ℕ) :
    ∑ e : Fin p, dimPartB L dim (topDimB L dim) (xs e j) =
      dimPartB L dim (topDimB L dim) x := by
  obtain ⟨hdisj, hU, -, -, -, hmem⟩ := h
  have hI : ∀ e, ∀ i ∈ I e, dim i = topDimB L dim := fun e i hi => by
    have : i ∈ Finset.univ.biUnion I := Finset.mem_biUnion.2 ⟨e, Finset.mem_univ _, hi⟩
    rw [hU] at this
    exact (Finset.mem_filter.1 this).2
  have h1 : ∀ e, dimPartB L dim (topDimB L dim) (xs e j) = ∑ i ∈ I e, L.σ i := fun e => by
    unfold dimPartB
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hi => (hmem e j i).1 hi.2, fun hi => ⟨hI e i hi, (hmem e j i).2 hi⟩⟩
  have h2 : dimPartB L dim (topDimB L dim) x = ∑ i ∈ IkB L dim, L.σ i := by
    unfold dimPartB IkB
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hi => hi.1, fun hi => ⟨hi, L.mem_M i⟩⟩
  rw [Finset.sum_congr rfl fun e _ => h1 e, h2, ← hU, Finset.sum_biUnion]
  intro e _ e' _ hne
  exact hdisj hne

end Gen

/-! ### The counterexample: two lines through `0` in `ℝ²` -/

/-- The lines `y = 0` and `y = x`. -/
def Mex : Fin 2 → Set (Fin 2 → ℝ) := ![graph2 (fun _ => (0 : ℝ)), graph2 (fun t : ℝ => t)]

theorem Mex_dim : ∀ i, (rnPolyfold 2).IsSubmanifoldOfDim (Mex i) 1 := by
  intro i
  fin_cases i
  · exact rnPolyfold_isSubmanifoldOfDim_graph2 contDiff_const
  · exact rnPolyfold_isSubmanifoldOfDim_graph2 contDiff_id

theorem Mex_closed : ∀ i, IsClosed (Mex i) := by
  intro i
  fin_cases i
  · exact isClosed_graph2 continuous_const
  · exact isClosed_graph2 continuous_id

theorem zero_mem_Mex : ∀ i, (0 : Fin 2 → ℝ) ∈ Mex i := by
  intro i
  fin_cases i
  · change (0 : Fin 2 → ℝ) 1 = 0; rfl
  · change (0 : Fin 2 → ℝ) 1 = (0 : Fin 2 → ℝ) 0; rfl

/-- The structure at `0` of `Θ = 1_{y=0} + 1_{y=x}`. -/
noncomputable def Lex := localBranchingStructure_sum_rn Mex 1 (fun _ => one_pos)
  (fun i => (Mex_dim i).1) Mex_closed 0

theorem not_B : ¬ B := by
  intro hB
  have hΘ := isBranchedEpSubgroupoid_sum_rn Mex 1 (fun _ => one_pos) (fun i => (Mex_dim i).1)
    Mex_closed
  set L := Lex with hLdef
  have hUuniv : ∀ y, y ∈ L.U := fun y i _ => zero_mem_Mex i
  let dim : L.ι → ℕ := fun _ => 1
  let i0 : L.ι := ⟨0, zero_mem_Mex 0⟩
  let i1 : L.ι := ⟨1, zero_mem_Mex 1⟩
  have hl : IsDimLabelB L dim := fun i m hm =>
    hasDimB_of (L.isSmoothSubmanifold i) (((Mex_dim i.1).inter_isOpen L.isOpen_U).2 m hm)
  have htop : topDimB L dim = 1 := Finset.sup_const ⟨i0, Finset.mem_univ _⟩ 1
  -- `0` is top-bad: near `0` the two lines differ
  have hbad : IsTopBadB L dim 0 := by
    refine ⟨mem_iUnion.2 ⟨i0, mem_iUnion.2 ⟨htop.symm, L.mem_M i0⟩⟩, ?_⟩
    rintro ⟨V, hV, h0V, hco⟩
    have heq := hco i0 i1 htop.symm htop.symm (L.mem_M i0) (L.mem_M i1)
    have hg : Continuous fun t : ℝ => t • (![1, 0] : Fin 2 → ℝ) :=
      continuous_id.smul continuous_const
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hV.preimage hg) 0
      (show (0 : ℝ) • (![1, 0] : Fin 2 → ℝ) ∈ V by rw [zero_smul]; exact h0V)
    have ht : (ε / 2) • (![1, 0] : Fin 2 → ℝ) ∈ V := by
      refine hball ?_
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
      exact half_lt_self hε
    have hm : (ε / 2) • (![1, 0] : Fin 2 → ℝ) ∈ V ∩ L.M i0 := by
      refine ⟨ht, ?_, hUuniv _⟩
      change ((ε / 2) • (![1, 0] : Fin 2 → ℝ)) 1 = 0
      simp
    rw [heq] at hm
    have h1 : ((ε / 2) • (![1, 0] : Fin 2 → ℝ)) 1 = ((ε / 2) • (![1, 0] : Fin 2 → ℝ)) 0 :=
      hm.2.1
    simp at h1
    linarith
  -- the two tangent lines differ
  have hT : TyMB (trivial (rnPolyfold 2)).PObj (L.M i0) 0 ≠
      TyMB (trivial (rnPolyfold 2)).PObj (L.M i1) 0 := by
    rw [tyMB_eq (L.mem_M i0), tyMB_eq (L.mem_M i1)]
    change (rnPolyfold 2).submanifoldTangent (graph2 (fun _ => (0 : ℝ)) ∩ L.U) 0 ≠
      (rnPolyfold 2).submanifoldTangent (graph2 (fun t : ℝ => t) ∩ L.U) 0
    rw [submanifoldTangent_inter_isOpen L.isOpen_U L.mem_U,
      submanifoldTangent_inter_isOpen L.isOpen_U L.mem_U]
    intro h
    have h' := congrArg (Set.image (chartVec idChart2)) h
    rw [chartVec_image_graph2 (β := fun _ : ℝ => (0 : ℝ)) contDiff_const (zero_mem_Mex 0),
      chartVec_image_graph2 (β := fun t : ℝ => t) contDiff_id (zero_mem_Mex 1)] at h'
    have hmem : graphDir (fun t : ℝ => t) 0 ∈
        (span ℝ {graphDir (fun _ : ℝ => (0 : ℝ)) 0} : Set ((rnChart 2 0).model.E 0)) := by
      rw [h']; exact subset_span (mem_singleton _)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
    change c • graphDirR (fun _ : ℝ => (0 : ℝ)) 0 = graphDirR (fun t : ℝ => t) 0 at hc
    have e1 := congrFun hc 1
    simp [graphDirR] at e1
  -- two classes
  have hik : ∀ i, i ∈ IkB L dim := fun i => by
    simp only [IkB, Finset.mem_filter, Finset.mem_univ, true_and]
    exact htop.symm
  have hC : 1 < (ClassesB L dim).card := by
    rw [Finset.one_lt_card]
    refine ⟨_, Finset.mem_image_of_mem _ (hik i0), _, Finset.mem_image_of_mem _ (hik i1), ?_⟩
    intro h
    have h1 : i1 ∈ (IkB L dim).filter (fun i => TyMB (trivial (rnPolyfold 2)).PObj (L.M i) 0 =
        TyMB (trivial (rnPolyfold 2)).PObj (L.M i1) 0) := Finset.mem_filter.2 ⟨hik i1, rfl⟩
    rw [← h] at h1
    exact hT (Finset.mem_filter.1 h1).2.symm
  -- `B` (i) gives data for every class, `B` (ii) the formula
  obtain ⟨hex, hform⟩ := hB (Fin 2 → ℝ) (Fin 2 → ℝ) (trivial (rnPolyfold 2)) _ hΘ 0 L dim hl hbad
  have : Nonempty L.ι := ⟨i0⟩
  choose! p I ie xs hdata using hex
  have h := hform p I ie xs hdata 0
  rw [Finset.sum_congr rfl fun Ξ hΞ => sum_dimPartB_of_isSliceDataB L dim (hdata Ξ hΞ) 0,
    Finset.sum_const, nsmul_eq_mul] at h
  have hpos : 0 < dimPartB L dim (topDimB L dim) 0 := by
    unfold dimPartB
    refine Finset.sum_pos (fun i _ => L.σ_pos i) ⟨i0, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨htop.symm, L.mem_M i0⟩
  have hC' : (2 : ℚ) ≤ (ClassesB L dim).card := by exact_mod_cast hC
  nlinarith

theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

/-- Ex falso (vacuous). -/
theorem B_to_A : B → A := fun h => (not_B h).elim

#rt_check RoundTrip.V9_62.not_B [Polyfold.EpGroupoid.LocalBranchingStructure.proposition_9_6_5,
  Polyfold.EpGroupoid.LocalBranchingStructure.sum_class_eq_sum_of_isTopSlice,
  Polyfold.EpGroupoid.LocalBranchingStructure.dimPart_topDim_eq_sum_slices,
  Polyfold.EpGroupoid.LocalBranchingStructure.sum_class_eq_of_hasGraphChartAt,
  Polyfold.EpGroupoid.LocalBranchingStructure.dimPart_topDim_eq_of_hasGraphChartAt]
#rt_check RoundTrip.V9_62.B_to_A [Polyfold.EpGroupoid.LocalBranchingStructure.proposition_9_6_5,
  Polyfold.EpGroupoid.LocalBranchingStructure.sum_class_eq_sum_of_isTopSlice,
  Polyfold.EpGroupoid.LocalBranchingStructure.dimPart_topDim_eq_sum_slices,
  Polyfold.EpGroupoid.LocalBranchingStructure.sum_class_eq_of_hasGraphChartAt,
  Polyfold.EpGroupoid.LocalBranchingStructure.dimPart_topDim_eq_of_hasGraphChartAt]
#rt_overlap RoundTrip.V9_62.B_to_A [Polyfold.EpGroupoid.LocalBranchingStructure.proposition_9_6_5,
  Polyfold.EpGroupoid.LocalBranchingStructure.sum_class_eq_sum_of_isTopSlice,
  Polyfold.EpGroupoid.LocalBranchingStructure.dimPart_topDim_eq_sum_slices,
  Polyfold.EpGroupoid.LocalBranchingStructure.sum_class_eq_of_hasGraphChartAt,
  Polyfold.EpGroupoid.LocalBranchingStructure.dimPart_topDim_eq_of_hasGraphChartAt]
#print axioms RoundTrip.V9_62.not_B

end RoundTrip.V9_62
