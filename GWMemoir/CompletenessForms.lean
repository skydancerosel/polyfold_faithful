import GWMemoir.Fibres
import GWMemoir.Completeness

/-!
# `SectionsClosed`, `ConstraintsClosed`, `FormsClosed` and the instances (Memoir p. 7, pp. 66–68)

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §1.2 (p. 7), §3.1
(pp. 66–68).

* **`sectionsClosed_of_nodes_empty`**, **`constraintsClosed_of_nodes_empty`**: `SectionsClosed`
  and `ConstraintsClosed` (`GWMemoir.SectionSpaces`) for a continuous map on a surface without
  nodes, for every atlas.  `exists_limit_section`: if `v n → w` in the block space and `v n`
  represents a continuous section `η n`, the disc representatives converge uniformly on the disc
  `r² < 1/8` (the Sobolev bound of `GWMemoir.Completeness`); the cores `r² ≤ 1/16` cover `S`,
  so `η n` converges at every point, and the limit is continuous, represented by `w`, and
  satisfies the constraints (the subspaces `H_{u(z)}` are closed).
* **`formsClosed`**: `FormsClosed` (`GWMemoir.Fibres`) holds for every atlas, nodes included.
  Along a subsequence (`exists_subseq_ae_fintype`) the finitely many blocks converge almost
  everywhere.  At a point `y`, the vectors on which the forms converge form a subspace
  (`convSub`); off the nodes it is `j`-invariant, hence `0` or the whole plane
  (`convSub_eq_bot_or_top`), and the limit form (`limitForm`) is anti-linear there.  Every vector
  a block reads (`T(∂_d)` in a disc, `∂_s σ` in a neck) is a vector of convergence wherever the
  cut-off is nonzero, because the tangent coordinate changes of `Q` are invertible there
  (`limitForm_coord`).  No regularity has to pass to the limit: the forms of the fibre are
  functions on `S`, constrained only by anti-linearity and their representatives.
  Consequences: `fibreSpace_eq_formsSub`, `mem_fibreScale_iff_rep`.
* Instances on the constant maps from the three-pointed sphere, for every atlas:
  `sphere3_sectionsClosed`, `sphere3_constraintsClosed`, `sphere3_formsClosed`.
* `sectionsDense_iff`, `formsDense_iff`: `SectionsDense` and `FormsDense` are the density of the
  smooth points in every level (the closedness is automatic for a closure).

## Readings

* `SectionsClosed`, `ConstraintsClosed`, `FormsClosed` are the memoir's completeness statements,
  not stronger ones: the norms of pp. 7 and 66 are the norms of the block spaces restricted to
  the representatives.
* `SectionsDense` and `FormsDense` are not proved here.  For an atlas with two overlapping discs,
  a smoothing of a section in one chart has to be controlled in `H^{3+m}` (resp. `H^{2+m}`) in
  the other chart.  The missing lemma is the change of disc charts at every level: for a smooth
  `c` with compact support in the strip and a diffeomorphism `ψ` near that support,
  `v ↦ c · (v ∘ ψ)` is bounded on `H^{k,δ}(ℝ × S¹)` for every `k` (the project has the case
  `ψ = id`, `c = c(s)`: `Polyfold/Chapter1/CylinderMultipliers.lean`).  With it and a smooth
  partition of unity on `S` subordinate to the disc regions, cut off by the partition, smooth
  each piece in its own chart (`dense_test`), and, for forms, project back to the anti-linear
  forms with `L ↦ ½(L - J L j)`.  On `sphere3` the charts are defined on all of `ℝ²`, so the
  transitions are smooth on the closed discs; for an atlas whose discs reach the boundary of the
  chart targets, the representatives of smooth sections need not lie in the blocks.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff
open Set Filter Topology MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. Sections: the limit of representatives -/

section Limit

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} {u : X.S → Q}

lemma isEmpty_neck_of_nodes_empty (hX : X.nodes = ∅) (A : SectionAtlas (E := E) X u) :
    IsEmpty (Fin A.nn) :=
  ⟨fun j => by obtain ⟨q, hq, -⟩ := A.node_nodal j; rw [hX] at hq; exact hq⟩

/-- **The limit of representatives** (no nodes): if `v n → w` in the block space and `v n`
represents the continuous section `η n`, then `η n` converges pointwise to a continuous section
represented by `w`.  The disc blocks lie in `H³ ⊂ C⁰`, so the convergence is uniform on the discs;
the cores of the discs cover `S`. -/
theorem exists_limit_section (hu : Continuous u) (hX : X.nodes = ∅)
    (A : SectionAtlas (E := E) X u) {δ : ℕ → ℝ} {h0 : 0 ≤ δ 0} {hmono : StrictMono δ}
    {v : ℕ → (blocks A δ h0 hmono) 0} {w : (blocks A δ h0 hmono) 0}
    (hv : Tendsto v atTop (𝓝 w)) {η : ℕ → Section E X} (hc : ∀ n, IsContSection u (η n))
    (hr : ∀ n, IsRep (η n) (v n)) :
    ∃ η' : Section E X, IsContSection u η' ∧ IsRep η' w ∧
      ∀ y, Tendsto (fun n => η n y) atTop (𝓝 (η' y)) := by
  have hnn := isEmpty_neck_of_nodes_empty hX A
  set hd := Neck.δ_nonneg δ h0 hmono 0
  have hb : ∀ i k, Tendsto (fun n => discBlock (v n) i k) atTop (𝓝 (discBlock w i k)) :=
    fun i k => (((continuous_apply (i, k)).comp continuous_fst).tendsto w).comp hv
  -- the sup bound on the discs
  have hF : ∀ n n' i k, ∀ p ∈ discD, |discRep A i k (η n) p - discRep A i k (η n') p| ≤
      3 * ‖discBlock (v n) i k - discBlock (v n') i k‖ := by
    intro n n' i k p hp
    refine abs_le_of_ae_eq_three (hδ := hd) _ isOpen_discD discD_sub
      ((continuousOn_discRep A hu (hc n) i k).sub (continuousOn_discRep A hu (hc n') i k)) ?_ p hp
    filter_upwards [val_sub_ae (discBlock (v n) i k) (discBlock (v n') i k), (hr n).1 i k,
      (hr n').1 i k] with x h1 h2 h3
    rw [h1, h2, h3]; rfl
  have hcauchy : ∀ i k, ∀ p ∈ discD, CauchySeq (fun n => discRep A i k (η n) p) := by
    intro i k p hp
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 (hb i k).cauchySeq (ε / 4) (by positivity)
    refine ⟨N, fun n hn n' hn' => ?_⟩
    rw [Real.dist_eq]
    have := hN n hn n' hn'
    rw [dist_eq_norm] at this
    linarith [hF n n' i k p hp]
  -- pointwise convergence of the sections
  have hconv : ∀ y, ∃ L, Tendsto (fun n => η n y) atTop (𝓝 L) := by
    intro y
    rcases A.cover y with ⟨i, p, hp, rfl⟩ | ⟨j, -⟩
    · have hpD := mem_discD_of_core hp
      set z := X.discPt (A.center i) (A.ε i) p
      have hk : ∀ k, ∃ c, Tendsto (fun n => crd k (tangentCoordChange 𝓘(ℝ, E) (u z)
          (u (A.center i)) (u z) (η n z))) atTop (𝓝 c) := by
        intro k
        obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete (hcauchy i k p hpD)
        refine ⟨c, hc.congr fun n => ?_⟩
        simp only [discRep, discCut_eq_one hp, one_mul]; rfl
      choose c hc using hk
      have h1 := ((tangentCoordChange 𝓘(ℝ, E) (u (A.center i)) (u z) (u z)).continuous.tendsto
        _).comp (tendsto_of_crd hc)
      refine ⟨_, h1.congr fun n => ?_⟩
      exact tcc_inv (A.disc_chart i p hpD).2 _
    · exact hnn.elim j
  choose η' hη' using hconv
  -- the representatives converge pointwise
  have hrep : ∀ i k p, Tendsto (fun n => discRep A i k (η n) p) atTop
      (𝓝 (discRep A i k η' p)) := by
    intro i k p
    exact tendsto_const_nhds.mul (((crd k).continuous_of_finiteDimensional.tendsto _).comp
      (((tangentCoordChange 𝓘(ℝ, E) _ _ _).continuous.tendsto _).comp (hη' _)))
  have hIsRep : IsRep η' w := by
    refine ⟨fun i k => ?_, fun j => hnn.elim j⟩
    exact ae_eq_of_tendsto_Lp (f := fun n => valCLM 3 hd (discBlock (v n) i k))
      (((valCLM 3 hd).continuous.tendsto _).comp (hb i k)) (fun n => (hr n).1 i k)
      (ae_of_all _ fun p => hrep i k p)
  refine ⟨η', fun x => ?_, hIsRep, hη'⟩
  -- continuity of the limit at `x`
  rcases A.cover x with ⟨i, p0, hp0, rfl⟩ | ⟨j, -⟩
  swap; · exact hnn.elim j
  have hp0D := mem_discD_of_core hp0
  set c := A.center i
  set ε := A.ε i
  have hεne : ε ≠ 0 := (A.ε_pos i).ne'
  -- uniform convergence on the disc
  have hunif : ∀ k, TendstoUniformlyOn (fun n => discRep A i k (η n)) (discRep A i k η') atTop
      discD := by
    intro k
    have hbd : ∀ n, ∀ p ∈ discD, |discRep A i k (η n) p - discRep A i k η' p| ≤
        3 * ‖discBlock (v n) i k - discBlock w i k‖ := by
      intro n p hp
      have h1 : Tendsto (fun n' => |discRep A i k (η n) p - discRep A i k (η n') p|) atTop
          (𝓝 |discRep A i k (η n) p - discRep A i k η' p|) :=
        (tendsto_const_nhds.sub (hrep i k p)).abs
      have h2 : Tendsto (fun n' => 3 * ‖discBlock (v n) i k - discBlock (v n') i k‖) atTop
          (𝓝 (3 * ‖discBlock (v n) i k - discBlock w i k‖)) :=
        ((tendsto_const_nhds.sub (hb i k)).norm).const_mul 3
      exact le_of_tendsto_of_tendsto h1 h2 (Eventually.of_forall fun n' => hF n n' i k p hp)
    rw [Metric.tendstoUniformlyOn_iff]
    intro e he
    have h3 : Tendsto (fun n => 3 * ‖discBlock (v n) i k - discBlock w i k‖) atTop (𝓝 0) := by
      have := ((tendsto_iff_norm_sub_tendsto_zero.1 (hb i k)).const_mul 3)
      simpa using this
    filter_upwards [(h3.eventually (gt_mem_nhds he))] with n hn p hp
    rw [dist_comm, Real.dist_eq]
    exact (hbd n p hp).trans_lt hn
  have hcontF : ∀ k, ContinuousOn (discRep A i k η') discD := fun k =>
    (hunif k).continuousOn (Frequently.of_forall fun n => continuousOn_discRep A hu (hc n) i k)
  set K : ℝ × ℝ → E := fun p => tangentCoordChange 𝓘(ℝ, E) (u (X.discPt c ε p)) (u c)
    (u (X.discPt c ε p)) (η' (X.discPt c ε p))
  have hK : ContinuousOn K discD := by
    have hk : ∀ k, ContinuousOn (fun p => crd k (K p)) discD := by
      intro k
      refine ((hcontF k).div continuous_discCut.continuousOn
        fun p hp => (discCut_pos hp).ne').congr fun p hp => ?_
      rw [Pi.div_apply, eq_div_iff (discCut_pos hp).ne']
      simp only [discRep, K]
      ring
    have e : K = fun p => ∑ k, crd k (K p) • Module.finBasis ℝ E k := by
      funext p
      conv_lhs => rw [← (Module.finBasis ℝ E).sum_repr (K p)]
      rfl
    rw [e]
    exact continuousOn_finsetSum _ fun k _ => (hk k).smul continuousOn_const
  -- read on `S` through the inverse of the disc chart
  set ψ : X.S → ℝ × ℝ := fun y => placeInv c ε (extChartAt 𝓘(ℝ, E2) c y)
  have htgt := (A.disc_chart i p0 hp0D).1
  have hxs : X.discPt c ε p0 ∈ (extChartAt 𝓘(ℝ, E2) c).source :=
    (extChartAt 𝓘(ℝ, E2) c).map_target htgt
  have hψx : ψ (X.discPt c ε p0) = p0 := by
    simp only [ψ, NodalSurface.discPt]
    rw [(extChartAt 𝓘(ℝ, E2) c).right_inv htgt, placeInv_place c hεne]
  have hψc : ContinuousAt ψ (X.discPt c ε p0) :=
    (continuous_placeInv c ε).continuousAt.comp (continuousAt_extChartAt' hxs)
  have hKψ : ContinuousAt (K ∘ ψ) (X.discPt c ε p0) :=
    ContinuousAt.comp_of_eq (hK.continuousAt (isOpen_discD.mem_nhds (hψx ▸ hp0D))) hψc hψx
  have hev : (K ∘ ψ) =ᶠ[𝓝 (X.discPt c ε p0)]
      fun y => tangentCoordChange 𝓘(ℝ, E) (u y) (u c) (u y) (η' y) := by
    filter_upwards [(isOpen_extChartAt_source c).mem_nhds hxs] with y hy
    have : X.discPt c ε (ψ y) = y := by
      simp only [ψ, NodalSurface.discPt]
      rw [place_placeInv c hεne, (extChartAt 𝓘(ℝ, E2) c).left_inv hy]
    simp only [Function.comp, K, this]
  exact continuousAt_coord_transfer hu (A.disc_chart i p0 hp0D).2 (mem_extChartAt_source _)
    (hKψ.congr hev)

end Limit

/-! ## 2. `SectionsClosed` and `ConstraintsClosed` without nodes -/

section Closed

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} {u : X.S → Q}

/-- **`SectionsClosed`** (Memoir p. 66, the completeness of the norm) for a continuous map `u`
on a surface without nodes, for every atlas. -/
theorem sectionsClosed_of_nodes_empty (hu : Continuous u) (hX : X.nodes = ∅)
    (A : SectionAtlas (E := E) X u) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ) :
    SectionsClosed A δ h0 hmono := by
  refine isClosed_of_closure_subset fun w hw => ?_
  obtain ⟨v, hvS, hv⟩ := mem_closure_iff_seq_limit.1 hw
  have hvS' : ∀ n, ∃ η : Section E X, IsContSection u η ∧ IsMatchingSection X η ∧
      IsRep η (v n) := hvS
  choose η hc _hm hr using hvS'
  obtain ⟨η', hc', hr', -⟩ := exists_limit_section hu hX A hv hc hr
  exact ⟨η', hc', fun x y hxy => by rw [hX] at hxy; exact absurd hxy (notMem_empty _), hr'⟩

/-- **`ConstraintsClosed`** (Memoir p. 68) for a continuous map on a surface without nodes:
the constraints pass to the pointwise limit. -/
theorem constraintsClosed_of_nodes_empty (hu : Continuous u) (hX : X.nodes = ∅)
    (A : SectionAtlas (E := E) X u) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)
    (C : LinearConstraints X E) : ConstraintsClosed A δ h0 hmono C := by
  refine isClosed_of_closure_subset fun w hw => ?_
  obtain ⟨v, hvS, hv⟩ := mem_closure_iff_seq_limit.1 hw
  have hvS' : ∀ n, ∃ η : Section E X, IsContSection u η ∧ IsMatchingSection X η ∧
      IsRep η (v n) ∧ ∀ l, (η (C.pt l) : E) ∈ C.H l := hvS
  choose η hc _hm hr hH using hvS'
  obtain ⟨η', hc', hr', hlim⟩ := exists_limit_section hu hX A hv hc hr
  refine ⟨η', hc', fun x y hxy => by rw [hX] at hxy; exact absurd hxy (notMem_empty _), hr',
    fun l => ?_⟩
  exact (C.H l).closed_of_finiteDimensional.mem_of_tendsto (hlim (C.pt l))
    (Eventually.of_forall fun n => hH n l)

/-- Without nodes, `H^{3,δ₀}_c(S, u*TQ)` is the set of representatives itself. -/
theorem sectionSpace_eq_of_nodes_empty (hu : Continuous u) (hX : X.nodes = ∅)
    (A : SectionAtlas (E := E) X u) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ) :
    sectionSpace A δ h0 hmono = sectionsSub A δ h0 hmono :=
  sectionSpace_eq A δ h0 hmono (sectionsClosed_of_nodes_empty hu hX A δ h0 hmono)

end Closed

/-! ## 3. A common a.e. subsequence for finitely many sequences in `L²` -/

section Subseq

/-- Finitely many sequences converging in `L²(ℝ × S¹)` have a common subsequence converging
almost everywhere. -/
theorem exists_subseq_ae_fintype {ι : Type} [Finite ι] {f : ι → ℕ → Lp ℝ 2 cyl}
    {g : ι → Lp ℝ 2 cyl} (hf : ∀ i, Tendsto (f i) atTop (𝓝 (g i))) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂cyl, ∀ i,
      Tendsto (fun k => (f i (ns k) : ℝ × ℝ → ℝ) x) atTop (𝓝 ((g i : ℝ × ℝ → ℝ) x)) := by
  have := Fintype.ofFinite ι
  have hm : TendstoInMeasure cyl (fun n x i => (f i n : ℝ × ℝ → ℝ) x) atTop
      (fun x i => (g i : ℝ × ℝ → ℝ) x) := by
    intro ε hε
    have hi : ∀ i, Tendsto (fun n => cyl {x | ε ≤ edist ((f i n : ℝ × ℝ → ℝ) x)
        ((g i : ℝ × ℝ → ℝ) x)}) atTop (𝓝 0) := fun i => tendstoInMeasure_of_tendsto_Lp (hf i) ε hε
    have hsum : Tendsto (fun n => ∑ i, cyl {x | ε ≤ edist ((f i n : ℝ × ℝ → ℝ) x)
        ((g i : ℝ × ℝ → ℝ) x)}) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum (Finset.univ) fun i _ => hi i
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun n => zero_le) fun n => ?_
    refine (measure_mono ?_).trans (measure_iUnion_fintype_le _ _)
    intro x hx
    simp only [mem_ofPred_eq, mem_iUnion] at hx ⊢
    by_contra hc
    push Not at hc
    rw [edist_pi_def] at hx
    exact absurd hx (not_le.2 ((Finset.sup_lt_iff hε).2 fun i _ => hc i))
  obtain ⟨ns, hns, hae⟩ := hm.exists_seq_tendsto_ae
  exact ⟨ns, hns, hae.mono fun x hx i => (tendsto_pi_nhds.1 hx) i⟩

end Subseq

/-! ## 4. Limits of linear maps along a sequence -/

section ConvLim

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (ζ : ℕ → E2 →L[ℝ] E)

/-- The vectors on which `ζ k` converges. -/
def convSub : Submodule ℝ E2 where
  carrier := {w | ∃ L, Tendsto (fun k => ζ k w) atTop (𝓝 L)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := fun ⟨L, hL⟩ ⟨L', hL'⟩ => ⟨L + L', by simpa using hL.add hL'⟩
  smul_mem' := fun c _ ⟨L, hL⟩ => ⟨c • L, by simpa using hL.const_smul c⟩

lemma tendsto_limUnder_convSub (w : convSub ζ) :
    Tendsto (fun k => ζ k w) atTop (𝓝 (limUnder atTop fun k => ζ k w)) :=
  tendsto_nhds_limUnder w.2

/-- The limit, a linear map on `convSub ζ`. -/
def convLim : convSub ζ →ₗ[ℝ] E where
  toFun w := limUnder atTop fun k => ζ k w
  map_add' w w' := by
    refine tendsto_nhds_unique (tendsto_limUnder_convSub ζ (w + w')) ?_
    have := (tendsto_limUnder_convSub ζ w).add (tendsto_limUnder_convSub ζ w')
    simpa using this
  map_smul' c w := by
    refine tendsto_nhds_unique (tendsto_limUnder_convSub ζ (c • w)) ?_
    have := (tendsto_limUnder_convSub ζ w).const_smul c
    simpa using this

lemma tendsto_convLim (w : convSub ζ) : Tendsto (fun k => ζ k w) atTop (𝓝 (convLim ζ w)) :=
  tendsto_limUnder_convSub ζ w

/-- A linear extension of the limit to `E2`. -/
def convExt : E2 →L[ℝ] E :=
  LinearMap.toContinuousLinearMap (Classical.choose (LinearMap.exists_extend (convLim ζ)))

lemma convExt_apply (w : E2) (hw : w ∈ convSub ζ) : convExt ζ w = convLim ζ ⟨w, hw⟩ := by
  have := congrArg (fun g => g ⟨w, hw⟩) (Classical.choose_spec (LinearMap.exists_extend
    (convLim ζ)))
  simpa [convExt] using this

end ConvLim

/-! ## 5. The limit form -/

section LimitForm

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) {m : ℕ} {X : NodalSurface m} {u : X.S → Q}

/-- Off the nodes, the vectors on which a sequence of anti-linear maps converges form a
`j`-invariant subspace of the plane, hence `0` or everything. -/
lemma convSub_eq_bot_or_top {y : X.S} {ζ : ℕ → E2 →L[ℝ] E}
    (hζ : ∀ k, ζ k ∈ X.antiLinearForms J (u y) y) : convSub ζ = ⊥ ∨ convSub ζ = ⊤ := by
  by_cases h : ∃ w ∈ convSub ζ, w ≠ 0
  · right
    obtain ⟨w, ⟨L, hL⟩, hw0⟩ := h
    have hjw : X.j.J y w ∈ convSub ζ := by
      refine ⟨-J.J (u y) L, ?_⟩
      have e : ∀ k, ζ k (X.j.J y w) = -J.J (u y) (ζ k w) := fun k => by
        have := (X.mem_antiLinearForms J).1 (hζ k) w
        rw [this, neg_neg]
      simp only [e]
      exact (((J.J (u y)).continuous.tendsto L).comp hL).neg
    have hli : LinearIndependent ℝ ![w, X.j.J y w] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h2 := congrArg (X.j.J y) hst
      simp only [map_add, map_smul, X.j.J_J, map_zero, smul_neg] at h2
      have h3 : (s ^ 2 + t ^ 2) • w = 0 := by
        have : (s ^ 2 + t ^ 2) • w = s • (s • w + t • X.j.J y w) - t • (s • X.j.J y w + -(t • w))
          := by
          simp only [smul_add, smul_neg, smul_smul, sub_eq_add_neg, neg_add, neg_neg, add_smul]
          abel_nf
          simp only [mul_comm, sq]
          abel
        rw [this, hst, h2]; simp
      rcases smul_eq_zero.1 h3 with h4 | h4
      · constructor <;> nlinarith [sq_nonneg s, sq_nonneg t]
      · exact absurd h4 hw0
    have hspan := hli.span_eq_top_of_card_eq_finrank (by simp)
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨L, hL⟩
    · exact hjw
  · left
    push Not at h
    exact (Submodule.eq_bot_iff _).2 h

open Classical in
/-- The limit form of a sequence of forms: at a point off the nodes it is the pointwise limit if
the maps converge on every vector and `0` otherwise; at a nodal point it is a linear extension of
the limit on the vectors where it exists. -/
def limitForm (ζ : ℕ → Form E X) : Form E X := fun y =>
  if convSub (fun k => ζ k y) ≠ ⊤ ∧ ∀ q ∈ X.nodes, y ∉ q then 0 else convExt (fun k => ζ k y)

/-- On every vector where `ζ k y` converges, `limitForm ζ y` is the limit. -/
lemma limitForm_tendsto {ζ : ℕ → Form E X} (hζ : ∀ k, IsAntiOff J X u (ζ k)) {y : X.S} {w : E2}
    (hw : w ∈ convSub fun k => ζ k y) :
    Tendsto (fun k => ζ k y w) atTop (𝓝 (limitForm ζ y w)) := by
  unfold limitForm
  split_ifs with h
  · rcases convSub_eq_bot_or_top J (u := u) (fun k => hζ k y h.2) with hb | ht
    · rw [hb, Submodule.mem_bot] at hw
      subst hw; simp
    · exact absurd ht h.1
  · rw [convExt_apply _ w hw]
    exact tendsto_convLim _ ⟨w, hw⟩

/-- The limit form is anti-linear off the nodes. -/
lemma limitForm_isAntiOff {ζ : ℕ → Form E X} (hζ : ∀ k, IsAntiOff J X u (ζ k)) :
    IsAntiOff J X u (limitForm ζ) := by
  intro y hy
  by_cases ht : convSub (fun k => ζ k y) = ⊤
  · rw [X.mem_antiLinearForms J]
    intro w
    have hw : ∀ w, w ∈ convSub fun k => ζ k y := fun w => ht ▸ Submodule.mem_top
    refine tendsto_nhds_unique (((J.J (u y)).continuous.tendsto _).comp
      (limitForm_tendsto J hζ (hw w))) ?_
    have e : ∀ k, J.J (u y) (ζ k y w) = -ζ k y (X.j.J y w) := fun k =>
      (X.mem_antiLinearForms J).1 (hζ k y hy) w
    simp only [Function.comp_def, e]
    exact (limitForm_tendsto J hζ (hw _)).neg
  · have : limitForm ζ y = 0 := by
      unfold limitForm; rw [if_pos ⟨ht, hy⟩]
    rw [this]; exact Submodule.zero_mem _

/-- **The pointwise step**: if the coordinates of `β · Γ(ζ k y w)` converge, with `Γ` a tangent
coordinate change of `Q` defined at `u(y)` (needed only when `β ≠ 0`), then `w` is a vector of
convergence and the limit form has the limit coordinates. -/
lemma limitForm_coord {ζ : ℕ → Form E X} (hζ : ∀ k, IsAntiOff J X u (ζ k)) {y : X.S} {b : Q}
    {w : E2} {β : ℝ} (hy : β ≠ 0 → u y ∈ (extChartAt 𝓘(ℝ, E) b).source)
    {c : Fin (Module.finrank ℝ E) → ℝ}
    (hk : ∀ k', Tendsto (fun n => β * crd k' (tangentCoordChange 𝓘(ℝ, E) (u y) b (u y)
      (ζ n y w))) atTop (𝓝 (c k'))) (k : Fin (Module.finrank ℝ E)) :
    β * crd k (tangentCoordChange 𝓘(ℝ, E) (u y) b (u y) (limitForm ζ y w)) = c k := by
  by_cases hβ : β = 0
  · subst hβ
    have := hk k
    simp only [zero_mul] at this
    rw [zero_mul]; exact tendsto_nhds_unique tendsto_const_nhds this
  · have hk' : ∀ k', Tendsto (fun n => crd k' (tangentCoordChange 𝓘(ℝ, E) (u y) b (u y)
        (ζ n y w))) atTop (𝓝 (c k' / β)) := fun k' => by
      have := (hk k').div_const β
      simpa [mul_div_cancel_left₀ _ hβ] using this
    have h1 := tendsto_of_crd hk'
    have h2 := ((tangentCoordChange 𝓘(ℝ, E) b (u y) (u y)).continuous.tendsto _).comp h1
    have hconv : w ∈ convSub fun n => ζ n y := ⟨_, h2.congr fun n => tcc_inv (hy hβ) _⟩
    have h3 := ((((crd k).continuous_of_finiteDimensional.comp
      (tangentCoordChange 𝓘(ℝ, E) (u y) b (u y)).continuous).tendsto _).comp
      (limitForm_tendsto J hζ hconv)).const_mul β
    exact tendsto_nhds_unique h3 (hk k)

end LimitForm

/-! ## 6. `FormsClosed` -/

section Closed

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) {m : ℕ} {X : NodalSurface m} {u : X.S → Q}
  (A : SectionAtlas (E := E) X u) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

/-- The blocks of an element of the fibre block space, as elements of `L²`. -/
def fBlockVal (v : (fibreBlocks A δ h0 hmono) 0) :
    (Fin A.nd × Fin 2 × Fin (Module.finrank ℝ E)) ⊕ (Fin A.nn × Fin (Module.finrank ℝ E)) →
      Lp ℝ 2 cyl
  | Sum.inl ⟨i, d, k⟩ => H.val (fDiscBlock v i d k)
  | Sum.inr ⟨j, k⟩ => H.val (fNeckBlock v j k)

variable {A δ h0 hmono} in
lemma tendsto_fBlockVal {v : ℕ → (fibreBlocks A δ h0 hmono) 0} {w : (fibreBlocks A δ h0 hmono) 0}
    (hv : Tendsto v atTop (𝓝 w)) (β) :
    Tendsto (fun n => fBlockVal A δ h0 hmono (v n) β) atTop (𝓝 (fBlockVal A δ h0 hmono w β)) := by
  rcases β with ⟨i, d, k⟩ | ⟨j, k⟩
  · exact (((valCLM 2 (Neck.δ_nonneg δ h0 hmono 0)).continuous.comp
      ((continuous_apply (i, d, k)).comp continuous_fst)).tendsto w).comp hv
  · exact (((valCLM 2 (Neck.δ_nonneg δ h0 hmono 0)).continuous.comp
      ((continuous_apply (j, k)).comp continuous_snd)).tendsto w).comp hv

/-- **`FormsClosed`** (the completeness of the fibre norm), for every atlas, nodes included.
A limit of representatives is the representative of a limit form: along a subsequence the blocks
converge almost everywhere, and at each point the forms converge on the vectors the blocks read
(`limitForm`).  The forms of the fibre are functions on `S` with no condition beyond
anti-linearity and their representatives, so no continuity has to pass to the limit. -/
theorem formsClosed : FormsClosed J A δ h0 hmono := by
  refine isClosed_of_closure_subset fun w hw => ?_
  obtain ⟨v, hvS, hv⟩ := mem_closure_iff_seq_limit.1 hw
  have hvS' : ∀ n, ∃ ξ : Form E X, IsAntiOff J X u ξ ∧ IsFormRep ξ (v n) := hvS
  choose ξ ha hr using hvS'
  obtain ⟨ns, -, hae⟩ := exists_subseq_ae_fintype (tendsto_fBlockVal hv)
  set ζ : ℕ → Form E X := fun k => ξ (ns k)
  have hζ : ∀ k, IsAntiOff J X u (ζ k) := fun k => ha (ns k)
  have hall : ∀ᵐ p ∂cyl, ∀ n,
      (∀ i d k, (H.val (fDiscBlock (v n) i d k) : ℝ × ℝ → ℝ) p = formDiscRep A i d k (ξ n) p) ∧
      ∀ j k, (H.val (fNeckBlock (v n) j k) : ℝ × ℝ → ℝ) p = formNeckRep A j k (ξ n) p := by
    rw [ae_all_iff]; intro n
    have h1 : ∀ᵐ p ∂cyl, ∀ i d k,
        (H.val (fDiscBlock (v n) i d k) : ℝ × ℝ → ℝ) p = formDiscRep A i d k (ξ n) p := by
      simp only [ae_all_iff]; exact (hr n).1
    have h2 : ∀ᵐ p ∂cyl, ∀ j k,
        (H.val (fNeckBlock (v n) j k) : ℝ × ℝ → ℝ) p = formNeckRep A j k (ξ n) p := by
      simp only [ae_all_iff]; exact (hr n).2
    filter_upwards [h1, h2] with p a b using ⟨a, b⟩
  refine ⟨limitForm ζ, limitForm_isAntiOff J hζ, fun i d k => ?_, fun j k => ?_⟩
  · filter_upwards [hae, hall] with p hp1 hp2
    set y := X.discPt (A.center i) (A.ε i) p
    have hlim : ∀ k', Tendsto (fun n => discCut p * crd k' (tangentCoordChange 𝓘(ℝ, E) (u y)
        (u (A.center i)) (u y) (ζ n y (tangentCoordChange 𝓘(ℝ, E2) (A.center i) y y
          (EuclideanSpace.single d 1))))) atTop
        (𝓝 ((H.val (fDiscBlock w i d k') : ℝ × ℝ → ℝ) p)) := fun k' =>
      (hp1 (Sum.inl (i, d, k'))).congr fun n => (hp2 (ns n)).1 i d k'
    exact (limitForm_coord J hζ (fun hβ => (A.disc_chart i p (discD_of_discCut_ne hβ)).2)
      hlim k).symm
  · filter_upwards [hae, hall] with p hp1 hp2
    set y := X.polar (A.hol j) p
    have hlim : ∀ k', Tendsto (fun n => Real.smoothTransition (p.1 - A.s0 j) *
        crd k' (tangentCoordChange 𝓘(ℝ, E) (u y) (u (A.node j)) (u y)
          (ζ n y (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar (A.hol j)) p (1, 0))))) atTop
        (𝓝 ((H.val (fNeckBlock w j k') : ℝ × ℝ → ℝ) p)) := fun k' =>
      (hp1 (Sum.inr (j, k'))).congr fun n => (hp2 (ns n)).2 j k'
    have hy : Real.smoothTransition (p.1 - A.s0 j) ≠ 0 →
        u y ∈ (extChartAt 𝓘(ℝ, E) (u (A.node j))).source := fun hβ => by
      refine (A.neck_chart j p ?_).2
      by_contra hc
      exact hβ (Real.smoothTransition.zero_of_nonpos (by linarith [not_le.1 hc]))
    exact (limitForm_coord J hζ hy hlim k).symm

/-- The fibre is the set of representatives itself, for every atlas. -/
theorem fibreSpace_eq_formsSub : fibreSpace J A δ h0 hmono = formsSub J A δ h0 hmono :=
  fibreSpace_eq J A δ h0 hmono (formsClosed J A δ h0 hmono)

/-- Level `m` of the fibre scale consists of the forms of class `(2+m, δ_m)`, for every atlas. -/
theorem mem_fibreScale_iff_rep (k : ℕ) (v : (fibreBlocks A δ h0 hmono) k) :
    v ∈ (fibreBlocks A δ h0 hmono).levelSub (fibreSpace J A δ h0 hmono) k ↔
      ∃ ξ : Form E X, IsAntiOff J X u ξ ∧ IsFormRep ξ ((fibreBlocks A δ h0 hmono).toBase k v) :=
  mem_fibreScale_iff J A δ h0 hmono (formsClosed J A δ h0 hmono) k v

end Closed

/-! ## 7. Instances and the density propositions -/

section Instances

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

/-- **Instance**: the constant maps from the three-pointed sphere, every atlas. -/
theorem sphere3_sectionsClosed (q : Q) (A : SectionAtlas (E := E) sphere3 (fun _ => q))
    (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ) : SectionsClosed A δ h0 hmono :=
  sectionsClosed_of_nodes_empty continuous_const rfl A δ h0 hmono

theorem sphere3_constraintsClosed (q : Q) (A : SectionAtlas (E := E) sphere3 (fun _ => q))
    (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ) (C : LinearConstraints sphere3 E) :
    ConstraintsClosed A δ h0 hmono C :=
  constraintsClosed_of_nodes_empty continuous_const rfl A δ h0 hmono C

theorem sphere3_formsClosed (J : AlmostComplexStructure E Q) (q : Q)
    (A : SectionAtlas (E := E) sphere3 (fun _ => q)) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0)
    (hmono : StrictMono δ) : FormsClosed J A δ h0 hmono :=
  formsClosed J A δ h0 hmono

variable {m : ℕ} {X : NodalSurface m} {u : X.S → Q} (A : SectionAtlas (E := E) X u)
  (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

/-- `SectionsDense` is the density of the smooth points in every level. -/
theorem sectionsDense_iff : SectionsDense A δ h0 hmono ↔ ∀ k,
    ((blocks A δ h0 hmono).levelSub (sectionSpace A δ h0 hmono) k : Set _) ⊆
      closure ((blocks A δ h0 hmono).levelSub (sectionSpace A δ h0 hmono) k ∩
        (blocks A δ h0 hmono).smoothLvl k) :=
  ⟨fun h => h.2, fun h => ⟨isClosed_sectionSpace A δ h0 hmono, h⟩⟩

/-- `FormsDense` is the density of the smooth points in every level. -/
theorem formsDense_iff (J : AlmostComplexStructure E Q) : FormsDense J A δ h0 hmono ↔ ∀ k,
    ((fibreBlocks A δ h0 hmono).levelSub (fibreSpace J A δ h0 hmono) k : Set _) ⊆
      closure ((fibreBlocks A δ h0 hmono).levelSub (fibreSpace J A δ h0 hmono) k ∩
        (fibreBlocks A δ h0 hmono).smoothLvl k) :=
  ⟨fun h => h.2, fun h => ⟨isClosed_fibreSpace J A δ h0 hmono, h⟩⟩

end Instances

end GWMemoir
