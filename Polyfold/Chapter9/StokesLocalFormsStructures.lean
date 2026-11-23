import Polyfold.Chapter9.BoundaryCover

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, **Remark 9.5.19, 2021 p. 451** (2017: Remark 9.8), point G.153.
Numbers and pages are the 2021 text's.

# Structures whose sheets are in the class of every space of forms

The classes `FormEval.sheets`, `FormEval.msheets` of the sheets over which the forms of a space
`Ω` are integrated depend on `Ω` (absolute integrability).  The proof of Theorem 9.5.18 with a
partition of unity near `supp Θ` (Remark 9.5.19) uses two spaces of forms and needs the structures
`U(x)` before the second space is known.  Here a condition on the sheet alone is given which puts
it in the class of every space of forms, and every oriented tame structure is restricted to one
with such sheets.

* `IsChartBounded X n N`: `N = N₀ ∩ V₁` with `N₀` in one graph chart, `V₁` open and `N` inside a
  compact subset of `N₀`; `IsChartBounded.mem_sheets`: then `N ∈ F.sheets` for every `F` (the
  proof of `FormEval.exists_mem_sheets`).
* `IsBoundedBoundary X Θ m B`: `B = ∂₁M ∩ V` inside a compact subset of a tame sheet
  `M ⊆ supp Θ` (the geometric hypothesis of `EP.boundaryStratum_inter_mem_msheets`).
* **`OrientedTameStructure.exists_restrict_all`**: every oriented tame structure describing `T̂Θ`
  restricts to one with these properties, with `x ∈ supp(∂Θ)` or `U(x)^*` disjoint from
  `supp(∂Θ)`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

open MPolyfold

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ} {T : Obj → X.PObj.OrTangent →₀ ℚ}

variable (X) in
/-- **A sheet in one graph chart inside a compact part of a larger one**: `N = N₀ ∩ V₁` with `N₀`
an `n`-dimensional submanifold in one graph chart, `V₁` open, and `N ⊆ K ⊆ N₀` for a compact
`K`. -/
def IsChartBounded (n : ℕ) (N : Set Obj) : Prop :=
  ∃ N₀ V₁ K : Set Obj, X.PObj.IsSubmanifoldOfDim N₀ n ∧ Nonempty (X.PObj.GraphChart n N₀) ∧
    IsOpen V₁ ∧ IsCompact K ∧ K ⊆ N₀ ∧ N₀ ∩ V₁ ⊆ K ∧ N = N₀ ∩ V₁

variable (X) in
/-- **A boundary sheet inside a compact part of a tame sheet in `supp Θ`**: `B = ∂₁M ∩ V` with
`M ⊆ supp Θ` an `(m+1)`-dimensional submanifold with tame induced structure, `V` open and
`B ⊆ K ⊆ M` for a compact `K`. -/
def IsBoundedBoundary (Θ : Obj → ℚ) (m : ℕ) (B : Set Obj) : Prop :=
  ∃ M V K : Set Obj, X.PObj.IsSubmanifoldOfDim M (m + 1) ∧ X.PObj.HasTameInducedStructure M ∧
    M ⊆ supp Θ ∧ IsOpen V ∧ IsCompact K ∧ K ⊆ M ∧ X.PObj.boundaryStratum M ∩ V ⊆ K ∧
    B = X.PObj.boundaryStratum M ∩ V

namespace IsChartBounded

variable {n : ℕ} {N : Set Obj}

theorem inter_isOpen (h : IsChartBounded X n N) {V : Set Obj} (hV : IsOpen V) :
    IsChartBounded X n (N ∩ V) := by
  obtain ⟨N₀, V₁, K, hN₀, hc, hV₁, hK, hKN, hsub, rfl⟩ := h
  exact ⟨N₀, V₁ ∩ V, K, hN₀, hc, hV₁.inter hV, hK, hKN,
    fun y hy => hsub ⟨hy.1, hy.2.1⟩, inter_assoc _ _ _⟩

/-- **Such a sheet is in the class of every space of forms**: the densities are continuous on
`N₀`, hence bounded on `K`, and the chart image of `N` has finite measure. -/
theorem mem_sheets {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω] (F : X.FormEval n Ω)
    (h : IsChartBounded X n N) : N ∈ F.sheets := by
  obtain ⟨N₀, V₁, K', hN₀, ⟨c₀⟩, hV₁o, hK'c, hK'N, hsub, rfl⟩ := h
  refine ⟨hN₀.inter_isOpen hV₁o, c₀.restrict hV₁o, fun ω => ?_⟩
  have hcont := F.continuousOn_ev_tvec hN₀.1 c₀ ω
  obtain ⟨C, hC⟩ := hK'c.exists_bound_of_continuousOn (hcont.mono hK'N)
  have hdom : (c₀.restrict hV₁o).dom = c₀.coord '' (N₀ ∩ V₁) := rfl
  have hfin : volume (c₀.restrict hV₁o).dom ≠ ⊤ := by
    have hcK : IsCompact (c₀.coord '' K') :=
      hK'c.image_of_continuousOn (c₀.continuousOn_coord.mono hK'N)
    exact (lt_of_le_of_lt (measure_mono (hdom ▸ image_mono hsub)) hcK.measure_lt_top).ne
  have hq : ∀ u ∈ (c₀.restrict hV₁o).dom, c₀.q u ∈ N₀ ∩ V₁ := fun u hu =>
    (c₀.restrict hV₁o).q_mem hu
  have hco : ContinuousOn (fun u => F.ev ω (c₀.tvec (c₀.q u))) (c₀.restrict hV₁o).dom :=
    hcont.comp ((c₀.restrict hV₁o).continuousOn_q) fun u hu => (hq u hu).1
  have : IsFiniteMeasure (volume.restrict (c₀.restrict hV₁o).dom) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hfin⟩
  refine Integrable.of_bound
    (hco.aestronglyMeasurable (c₀.restrict hV₁o).measurableSet_dom') C ?_
  refine (ae_restrict_iff' (c₀.restrict hV₁o).measurableSet_dom').2 (Eventually.of_forall ?_)
  intro u hu
  exact hC _ (hsub (hq u hu))

end IsChartBounded

/-- **Every point of an `n`-dimensional submanifold has a neighbourhood in which the submanifold
is a sheet in the class of every space of forms.** -/
theorem exists_isChartBounded {n : ℕ} {N : Set Obj} (hN : X.PObj.IsSubmanifoldOfDim N n)
    {x : Obj} (hx : x ∈ N) : ∃ V : Set Obj, IsOpen V ∧ x ∈ V ∧ IsChartBounded X n (N ∩ V) := by
  obtain ⟨V₀, hV₀, hxV₀, hc₀⟩ := MPolyfold.exists_graphChart hN hx
  obtain ⟨W, hW, hxW, Kx, hKx, hNW, hKxN⟩ := MPolyfold.exists_compact_nhds_submanifold hN hx
  obtain ⟨t, ht, htc, htV⟩ := exists_mem_nhds_isClosed_subset (hV₀.mem_nhds hxV₀)
  refine ⟨V₀ ∩ (interior t ∩ W), hV₀.inter (isOpen_interior.inter hW),
    ⟨hxV₀, mem_interior_iff_mem_nhds.2 ht, hxW⟩, N ∩ V₀, interior t ∩ W, Kx ∩ t,
    hN.inter_isOpen hV₀, hc₀, isOpen_interior.inter hW, hKx.inter_right htc,
    fun y hy => ⟨hKxN hy.1, htV hy.2⟩,
    fun y hy => ⟨hNW ⟨hy.1.1, hy.2.2⟩, interior_subset hy.2.1⟩, (inter_assoc _ _ _).symm⟩

namespace OrientedTameStructure

/-- **Every oriented tame structure restricts to one whose sheets are in the class of every space
of forms, with boundary sheets inside compact parts of tame sheets** (`Θ` compact, of dimension
`m + 1`), and with `x ∈ supp(∂Θ)` or `U(x)^*` disjoint from `supp(∂Θ)`; the natural action of the
restriction is a restriction of the given one. -/
theorem exists_restrict_all {m : ℕ} (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) (hnd : X.IsNDimensional Θ (m + 1)) {x : Obj}
    (C₀ : X.OrientedTameStructure (m + 1) Θ x) (hC₀ : C₀.Represents T) :
    ∃ C : X.OrientedTameStructure (m + 1) Θ x, C.Represents T ∧
      (∀ i, IsChartBounded X (m + 1) (C.M i)) ∧
      (∀ i, IsBoundedBoundary X Θ m (C.boundarySheet i)) ∧
      (x ∈ supp (X.boundaryTheta Θ) ∨
        Disjoint (X.π ⁻¹' (X.π '' C.U)) (supp (X.boundaryTheta Θ))) ∧
      C.rep.U ⊆ C₀.rep.U ∧ C.rep.Φ = C₀.rep.Φ := by
  choose V hV hxV hVS using fun i =>
    exists_isChartBounded (C₀.isSubmanifoldOfDim i) (C₀.mem_M i)
  obtain ⟨C₁, hC₁, hC₁W, -, hC₁M, hU₁, hΦ₁⟩ := C₀.exists_restrict_eq hC₀
    (isOpen_iInter_of_finite hV) (mem_iInter.2 hxV)
  have hS₁ : ∀ j, IsChartBounded X (m + 1) (C₁.M j) := fun j => by
    obtain ⟨i, hi⟩ := hC₁M j
    have e : C₁.M j = (C₀.M i ∩ V i) ∩ C₁.U := by
      rw [hi, inter_assoc, inter_eq_right.2 fun y hy => mem_iInter.1 (hC₁W hy) i]
    rw [e]
    exact (hVS i).inter_isOpen C₁.isOpen_U
  obtain ⟨K, hK, hUK, -⟩ :=
    exists_isCompact_supp_inter hΘ.isFunctorial hcpt hnd C₁.hasPropernessProperty.2
  obtain ⟨t, htn, htc, htU⟩ := exists_mem_nhds_isClosed_subset (C₁.isOpen_U.mem_nhds C₁.mem_U)
  obtain ⟨W, hWo, hxW, hW⟩ : ∃ W : Set Obj, IsOpen W ∧ x ∈ W ∧
      (x ∈ supp (X.boundaryTheta Θ) ∨ W ⊆ (X.π ⁻¹' X.orbitSupp (X.boundaryTheta Θ))ᶜ) := by
    by_cases hxb : x ∈ supp (X.boundaryTheta Θ)
    · exact ⟨univ, isOpen_univ, mem_univ x, Or.inl hxb⟩
    · exact ⟨_, isOpen_compl_preimage_orbitSupp_boundaryTheta hΘ hcpt,
        mem_compl_preimage_orbitSupp_boundaryTheta hΘ hxb, Or.inr subset_rfl⟩
  obtain ⟨C, hCT, hCW, -, hCM, hrepU, hrepΦ⟩ := C₁.exists_restrict_eq hC₁
    (isOpen_interior.inter hWo) ⟨mem_interior_iff_mem_nhds.2 htn, hxW⟩
  refine ⟨C, hCT, fun i => ?_, fun i => ?_, hW.imp id fun h =>
    disjoint_preimage_image_supp_boundaryTheta fun y hy => h (hCW hy).2,
    hrepU.trans hU₁, hrepΦ.trans hΦ₁⟩
  · obtain ⟨j, hj⟩ := hCM i
    rw [hj]
    exact (hS₁ j).inter_isOpen C.isOpen_U
  · obtain ⟨j, hj⟩ := hCM i
    have hb : C.boundarySheet i = X.PObj.boundaryStratum (C₁.M j) ∩ C.U := by
      change X.PObj.boundaryStratum (C.M i) = _
      rw [hj, MPolyfold.boundaryStratum_inter_isOpen C.isOpen_U]
    refine ⟨C₁.M j, C.U, C₁.M j ∩ (K ∩ t), C₁.isSubmanifoldOfDim j,
      C₁.hasTameInducedStructure j,
      C₁.toTameBranchingStructure.toLocalBranchingStructure.M_subset_supp j, C.isOpen_U,
      C₁.toLocalBranchingStructure.isCompact_M_inter j (hK.inter_right htc)
        fun y hy => htU hy.2, inter_subset_left, ?_, hb⟩
    rintro y ⟨hy, hyU⟩
    have hyM : y ∈ C₁.M j := hy.1
    exact ⟨hyM, hUK ⟨C₁.toLocalBranchingStructure.M_subset_supp j hyM, C₁.subset_U j hyM⟩,
      interior_subset (hCW hyU).1⟩

end OrientedTameStructure

end EpGroupoid

end Polyfold
