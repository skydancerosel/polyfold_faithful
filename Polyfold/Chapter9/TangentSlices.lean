import Polyfold.Chapter9.TangentSlicesRn
import Polyfold.Chapter8.TangentOrbit

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.2: **Lemma 9.2.7** (p. 412; 2017: Lemma 9.5, p. 300), the density half of
(1) and part (2), and the hypotheses of **Definition 9.2.12** (p. 418; 2017: Definition 9.6,
p. 306).  The chart description of tangent spaces and the tangent slices of Proposition 9.2.8
are in `TangentSlicesBasic.lean`, the case of `ℝᵐ` in `TangentSlicesRn.lean`.

# Good points are dense; the tangent `TMᵢ`

## The text, paraphrased

(Lemma 9.2.7) (1) The good points are open and dense in `supp(Θ)`, the bad points closed and
nowhere dense; (2) at a bad `x`, every `Mᵢ` of a local branching structure contains a sequence
of good points converging to `x`.  *Proof* of (2): with `Σᵢ = Mᵢ ∩ Mᵢ₀ ∩ D_k(x)`, either a point
of `Mᵢ₀ ∩ D_k(x)` avoids all `Σᵢ`, or some `Σᵢ` has interior and a point can be moved off the
boundaries; such a point is "clearly" good.  (Definition 9.2.12) The local branching structure of
`TΘ` is `(TMᵢ)`, `(σᵢ)`.

## What is formalized

* `exists_isOpen_subset_inter_eq_empty_or_subset` (moving a point off the `Σᵢ`, one at a time).
* **Lemma 9.2.7 (1)**: `lemma_9_2_7_1_dense` (`S^g_Θ` dense, `S^b_Θ` nowhere dense in
  `supp(Θ)`), through `dense_goodSet`, `isNowhereDense_badSet`; the openness half is
  `lemma_9_2_7_1` (`GoodPoints.lean`).  No dimension hypothesis is used.
* **Lemma 9.2.7 (2)**: `lemma_9_2_7_2`, for `n`-dimensional `Mᵢ`, under invariance of domain
  (`MPolyfold.HasDomainInvarianceAt`); it holds in `ℝᵐ` (`hasDomainInvarianceAt_rn`), so
  `lemma_9_2_7_2_rn` has no further hypothesis.  Nontrivial instance: the origin is a bad point
  of the `Θ` of Remark 9.1.3 (b) (`Remark913Hyp.zero_mem_badSet`), with good points converging
  to it on each graph (`Remark913Hyp.exists_seq_goodSet_structureβ`).
* **Definition 9.2.12**: of `TangentBranchingHyp`, the closedness of `TMᵢ` in `TU(x)` is proved
  (`isClosed_tangentSubmanifold`), the paracompactness of `|supp(TΘ)|` follows from that of
  `|X|` (`paracompactSpace_orbitSupp_tangentTheta`), and `TMᵢ ⊆ (TX)_∞` from the submanifold
  property; `tangentBranchingHyp_of_isSmoothSubmanifold`,
  `isBranchedEpSubgroupoid_tangentTheta_of_isSmoothSubmanifold`.

## What the text leaves implicit, and the choices made

* Lemma 9.2.7 (1) is derived in the text from (2); its density half needs neither (2) nor
  equidimensionality: a neighbourhood meeting each `Mⱼ` in all of `M_U` or not at all consists
  of good points.
* In (2) the point found is good only if `Mᵢ₀ ⊆ Mᵢ` near it forces `Mᵢ₀ = Mᵢ` near it: invariance
  of domain for submanifolds of equal dimension, a Part I fact taken as the hypothesis
  `HasDomainInvarianceAt`.  The statement holds at every `x`, bad or not.
* Left open: that the `TMᵢ` are smooth submanifolds of `TX` (the tangent of an sc⁺-retraction is
  an sc⁺-retraction of `TX`), the only field of `TangentBranchingHyp` not derived here.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Module
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u

/-! ### Invariance of domain for submanifolds of equal dimension -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

variable (P) in
/-- **Invariance of domain at `y` in dimension `n`**: an `n`-dimensional submanifold `A ∋ y`
contained near `y` in an `n`-dimensional submanifold `B` agrees with `B` near `y`.  (Used in the
proof of Lemma 9.2.7 (2), where a point of `Mᵢ₀` inside `Σᵢ` is "clearly" good.) -/
def HasDomainInvarianceAt (y : X) (n : ℕ) : Prop :=
  ∀ A B : Set X, P.IsSubmanifoldOfDim A n → P.IsSubmanifoldOfDim B n → y ∈ A →
    ∀ V ∈ 𝓝 y, A ∩ V ⊆ B → ∃ V' ∈ 𝓝 y, B ∩ V' ⊆ A

variable {m : ℕ}

/-- The derivative of a `C^∞` retraction of `ℝᵐ` at a fixed point is a projection onto its
range. -/
theorem rn_retraction_deriv {W : Set (Fin m → ℝ)} (hWo : IsOpen W) {x : Fin m → ℝ} (hxW : x ∈ W)
    {s : (Fin m → ℝ) → Fin m → ℝ} (hsm : ContDiffOn ℝ ∞ s W) (hidem : ∀ y ∈ W, s (s y) = s y)
    (hsx : s x = x) :
    HasStrictFDerivAt s (fderiv ℝ s x) x ∧ ∀ c ∈ range (fderiv ℝ s x), fderiv ℝ s x c = c := by
  have hstrict : HasStrictFDerivAt s (fderiv ℝ s x) x :=
    (hsm.contDiffAt (hWo.mem_nhds hxW)).hasStrictFDerivAt (by simp)
  refine ⟨hstrict, ?_⟩
  set D := fderiv ℝ s x
  have hDD : D.comp D = D := by
    have h' : HasFDerivAt s D (s x) := by rw [hsx]; exact hstrict.hasFDerivAt
    have hcomp : HasFDerivAt (s ∘ s) (D.comp D) x := h'.comp x hstrict.hasFDerivAt
    have hev : s =ᶠ[𝓝 x] s ∘ s :=
      Filter.eventually_of_mem (hWo.mem_nhds hxW) fun y hy => (hidem y hy).symm
    exact (hcomp.congr_of_eventuallyEq hev).unique hstrict.hasFDerivAt
  rintro _ ⟨y, rfl⟩
  exact congrArg (fun L : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) => L y) hDD

/-- **Invariance of domain holds in `ℝᵐ`** (nontrivial witness of `HasDomainInvarianceAt`): if
`A ∩ V ⊆ B` with `A`, `B` of dimension `n`, then `T_yA = T_yB` (equal dimension), both are graphs
over this space near `y`, and every `b ∈ B` near `y` equals the point of `A` over the same
foot. -/
theorem hasDomainInvarianceAt_rn (y : Fin m → ℝ) (n : ℕ) :
    (rnPolyfold m).HasDomainInvarianceAt y n := by
  intro A B hA hB hyA V hV hAB
  obtain ⟨V₀, hV₀V, hV₀o, hyV₀⟩ := mem_nhds_iff.1 hV
  have hyB : y ∈ B := hAB ⟨hyA, mem_of_mem_nhds hV⟩
  have hφ := isChart_rnChart (n := m) 0
  obtain ⟨WA, hWAo, hyWA, sA, hsA, -, hidA, himgA, hTA⟩ := rn_exists_retraction hA.1 hyA
  obtain ⟨WB, hWBo, hyWB, sB, hsB, -, hidB, himgB, hTB⟩ := rn_exists_retraction hB.1 hyB
  have hfixA : ∀ a ∈ WA ∩ A, sA a = a := fun a ha => by
    rw [← himgA] at ha; obtain ⟨w, hw, rfl⟩ := ha; exact hidA w hw
  have hfixB : ∀ a ∈ WB ∩ B, sB a = a := fun a ha => by
    rw [← himgB] at ha; obtain ⟨w, hw, rfl⟩ := ha; exact hidB w hw
  -- the tangent spaces agree
  have hsub : (rnPolyfold m).chartTangent hφ A y ⊆ (rnPolyfold m).chartTangent hφ B y :=
    (chartTangent_subset_iff hφ (mem_univ y)).2
      (submanifoldTangent_subset_of_subset hB.1 hV₀o hyV₀ fun z hz => hAB ⟨hz.1, hV₀V hz.2⟩)
  obtain ⟨NA, hNA, hfinA⟩ := exists_submodule_chartTangent hφ hA.1 hyA (mem_univ y)
  obtain ⟨NB, hNB, hfinB⟩ := exists_submodule_chartTangent hφ hB.1 hyB (mem_univ y)
  have hrA := finrank_chartTangent hφ (hA.2 y hyA) hA.1 (mem_univ y) hNA
  have hrB := finrank_chartTangent hφ (hB.2 y hyB) hB.1 (mem_univ y) hNB
  have hle : NA ≤ NB := fun v hv => by
    have : v ∈ (NB : Set ((rnChart m 0).model.E 0)) := by
      rw [hNB]; exact hsub (by rw [← hNA]; exact hv)
    exact this
  have hNeq : NA = NB := Submodule.eq_of_le_of_finrank_eq hle (by rw [hrA, hrB])
  have hT : range (fderiv ℝ sA y) = range (fderiv ℝ sB y) := by
    rw [← hTA, ← hTB, ← hNA, ← hNB, hNeq]
  obtain ⟨hstA, hDA⟩ := rn_retraction_deriv hWAo hyWA hsA hidA (hfixA y ⟨hyWA, hyA⟩)
  obtain ⟨hstB, hDB⟩ := rn_retraction_deriv hWBo hyWB hsB hidB (hfixB y ⟨hyWB, hyB⟩)
  set DA := fderiv ℝ sA y with hDAdef
  set Q := fderiv ℝ sB y with hQdef
  set N : Submodule ℝ (Fin m → ℝ) := LinearMap.range (DA : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    with hNdef
  have hmemN : ∀ v, v ∈ N ↔ v ∈ range DA := fun v => by
    rw [hNdef, LinearMap.mem_range]; rfl
  have hQN : ∀ v, Q v ∈ N := fun v => (hmemN _).2 (hT ▸ ⟨v, rfl⟩)
  have hQid : ∀ v ∈ N, Q v = v := fun v hv => hDB v (hT ▸ (hmemN v).1 hv)
  -- the radii
  obtain ⟨ρA, hρA, hρAsub⟩ := Metric.isOpen_iff.1 (hWAo.inter hV₀o) y ⟨hyWA, hyV₀⟩
  obtain ⟨r, hr, hgr⟩ := exists_mem_graph_of_hasStrictFDerivAt hstA (hfixA y ⟨hyWA, hyA⟩)
    (N := N) (fun c hc => hDA c ((hmemN c).1 hc)) hQN hQid one_pos hρA
  set c₀ := ‖ContinuousLinearMap.id ℝ (Fin m → ℝ) - Q‖ with hc₀def
  set η : ℝ := 1 / (2 * (c₀ + 1)) with hηdef
  have hη : 0 < η := by positivity
  have hηc : η * c₀ < 1 := by
    rw [hηdef, div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
    linarith [norm_nonneg (ContinuousLinearMap.id ℝ (Fin m → ℝ) - Q)]
  obtain ⟨δB, hδB, hestB⟩ := Metric.eventually_nhds_iff.1 (hstB.isLittleO.def hη)
  obtain ⟨ρB, hρB, hρBsub⟩ := Metric.isOpen_iff.1 hWBo y hyWB
  set q := ‖Q‖ + 1 with hqdef
  have hq : 1 ≤ q := by rw [hqdef]; linarith [norm_nonneg Q]
  set μ := min (r / q) (min ρA (min δB ρB)) with hμdef
  have hμ : 0 < μ := lt_min (by positivity) (lt_min hρA (lt_min hδB hρB))
  have hμr : μ ≤ r / q := min_le_left _ _
  have hμA : μ ≤ ρA := (min_le_right _ _).trans (min_le_left _ _)
  have hμδ : μ ≤ δB := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hμB : μ ≤ ρB := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hrq : r / q ≤ r := div_le_self hr.le hq
  refine ⟨Metric.ball y (μ / (2 * q)), Metric.ball_mem_nhds _ (by positivity), ?_⟩
  rintro b ⟨hbB, hb⟩
  rw [Metric.mem_ball, dist_eq_norm] at hb
  have h2q : μ / (2 * q) ≤ μ := div_le_self hμ.le (by linarith)
  have hqb : q * ‖b - y‖ < μ / 2 := by
    calc q * ‖b - y‖ < q * (μ / (2 * q)) := mul_lt_mul_of_pos_left hb (by linarith)
      _ = μ / 2 := by field_simp
  set u := Q (b - y) with hudef
  have hu_le : ‖u‖ ≤ q * ‖b - y‖ :=
    (Q.le_opNorm _).trans (mul_le_mul_of_nonneg_right (by rw [hqdef]; linarith)
      (norm_nonneg _))
  have hur : ‖u‖ < r := by linarith
  obtain ⟨c, -, hcρ, hQc, hest⟩ := hgr u (hQN _) hur
  set a := sA (y + c) with hadef
  have hyc : y + c ∈ WA ∩ V₀ := hρAsub (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hcρ)
  have haA : a ∈ A := by
    have : a ∈ sA '' WA := ⟨y + c, hyc.1, rfl⟩
    rw [himgA] at this; exact this.2
  have hay : ‖a - y‖ < μ := by
    have h1 : ‖a - y‖ ≤ ‖(a - y) - u‖ + ‖u‖ := by
      calc ‖a - y‖ = ‖((a - y) - u) + u‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    linarith
  have haV : a ∈ V₀ := (hρAsub (by rw [Metric.mem_ball, dist_eq_norm]; linarith)).2
  have haB : a ∈ B := hAB ⟨haA, hV₀V haV⟩
  have haWB : a ∈ WB := hρBsub (by rw [Metric.mem_ball, dist_eq_norm]; linarith)
  have hbWB : b ∈ WB := hρBsub (by rw [Metric.mem_ball, dist_eq_norm]; linarith)
  have h := hestB (y := (a, b)) (by
    rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm]
    exact max_lt (by linarith) (by linarith))
  dsimp only at h
  rw [hfixB a ⟨haWB, haB⟩, hfixB b ⟨hbWB, hbB⟩] at h
  have hQab : Q (a - b) = 0 := by
    have : a - b = (a - y) - (b - y) := by abel
    rw [this, map_sub, hQc, ← hudef, sub_self]
  have h0 := eq_zero_of_proj_eq_zero (T := range Q) hDB hQab ⟨a - b, rfl⟩ hηc h
  rw [sub_eq_zero] at h0
  exact h0 ▸ haA

end MPolyfold

/-! ### Lemma 9.2.7 -/

/-- **The shrinking step of the proof of Lemma 9.2.7 (2)** (2021 pp. 412–413): for finitely many
`M_j` closed in an open `U` and an open `S ⊆ U` meeting `Y`, some open `S' ⊆ S` still meets `Y`, and
for every `j` either `S' ∩ Y` misses `M_j` or lies in `M_j` (remove the `M_j` one at a time). -/
theorem exists_isOpen_subset_inter_eq_empty_or_subset {Z : Type*} [TopologicalSpace Z]
    {ι : Type*} [Finite ι] {U : Set Z} (M : ι → Set Z) (hM : ∀ j, IsOpen (U \ M j)) {S Y : Set Z}
    (hS : IsOpen S) (hSU : S ⊆ U) (hSY : (S ∩ Y).Nonempty) :
    ∃ S' ⊆ S, IsOpen S' ∧ (S' ∩ Y).Nonempty ∧ ∀ j, S' ∩ Y ∩ M j = ∅ ∨ S' ∩ Y ⊆ M j := by
  classical
  cases nonempty_fintype ι
  suffices h : ∀ F : Finset ι, ∃ S' ⊆ S, IsOpen S' ∧ (S' ∩ Y).Nonempty ∧
      ∀ j ∈ F, S' ∩ Y ∩ M j = ∅ ∨ S' ∩ Y ⊆ M j by
    obtain ⟨S', h1, h2, h3, h4⟩ := h Finset.univ
    exact ⟨S', h1, h2, h3, fun j => h4 j (Finset.mem_univ j)⟩
  intro F
  induction F using Finset.induction_on with
  | empty => exact ⟨S, subset_rfl, hS, hSY, fun j hj => absurd hj (Finset.notMem_empty j)⟩
  | insert j F _ ih =>
    obtain ⟨S', hS'S, hS'o, hS'Y, hS'F⟩ := ih
    by_cases hsub : S' ∩ Y ⊆ M j
    · refine ⟨S', hS'S, hS'o, hS'Y, fun j' hj' => ?_⟩
      rcases Finset.mem_insert.1 hj' with rfl | hj'
      · exact Or.inr hsub
      · exact hS'F j' hj'
    · obtain ⟨z, hz, hzj⟩ := not_subset.1 hsub
      refine ⟨S' ∩ (U \ M j), inter_subset_left.trans hS'S, hS'o.inter (hM j),
        ⟨z, ⟨hz.1, hSU (hS'S hz.1), hzj⟩, hz.2⟩, fun j' hj' => ?_⟩
      rcases Finset.mem_insert.1 hj' with rfl | hj'
      · exact Or.inl (eq_empty_of_forall_notMem fun w hw => hw.1.1.2.2 hw.2)
      · rcases hS'F j' hj' with h | h
        · exact Or.inl (eq_empty_of_forall_notMem fun w hw =>
            (h ▸ ⟨⟨hw.1.1.1, hw.1.2⟩, hw.2⟩ : w ∈ (∅ : Set Z)))
        · exact Or.inr fun w hw => h ⟨hw.1.1, hw.2⟩

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ}

/-- **Lemma 9.2.7 (1), the density of `S^g_Θ`**: the good points are dense in `supp(Θ)`.  In a local
branching structure at `y ∈ supp(Θ)`, shrink a neighbourhood of `y` until it meets each `Mⱼ` in all
of `M_U` or not at all (`exists_isOpen_subset_inter_eq_empty_or_subset`); its points of `M_U` are
good.  No dimension hypothesis is needed. -/
theorem dense_goodSet (hΘ : X.IsBranchedEpSubgroupoid Θ) :
    Dense ((↑) ⁻¹' X.goodSet Θ : Set (supp Θ)) := by
  refine dense_iff_inter_open.2 fun O' hO' ⟨y, hyO'⟩ => ?_
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.1 hO'
  obtain ⟨B⟩ := hΘ.localBranching y.1 y.2
  have hyMU : y.1 ∈ B.MU := by rw [B.MU_eq]; exact ⟨y.2, B.mem_U⟩
  obtain ⟨S', hS'S, hS'o, ⟨z, hzS', hzMU⟩, hj⟩ :=
    exists_isOpen_subset_inter_eq_empty_or_subset B.M B.isOpen_U_diff_M (hO.inter B.isOpen_U)
      inter_subset_right ⟨y.1, ⟨hyO', B.mem_U⟩, hyMU⟩
  have hzsupp : z ∈ supp Θ := by rw [B.MU_eq] at hzMU; exact hzMU.1
  have hzU : z ∈ B.U := (hS'S hzS').2
  have hcover : ∀ i, z ∈ B.M i → S' ∩ B.M i = S' ∩ B.MU := fun i hzi => by
    have hsub : S' ∩ B.MU ⊆ B.M i := by
      rcases hj i with h | h
      · exact absurd (h ▸ ⟨⟨hzS', hzMU⟩, hzi⟩ : z ∈ (∅ : Set Obj)) (notMem_empty z)
      · exact h
    refine Subset.antisymm (fun w hw => ⟨hw.1, mem_iUnion.2 ⟨i, hw.2⟩⟩) fun w hw =>
      ⟨hw.1, hsub hw⟩
  refine ⟨⟨z, hzsupp⟩, (hS'S hzS').1, hzsupp, y.1, B, hzU, hzMU, S', hS'o, hzS',
    fun w hw => (hS'S hw).2, fun i j hzi hzj => ?_⟩
  rw [hcover i hzi, hcover j hzj]

/-- **Lemma 9.2.7 (1), the nowhere density of `S^b_Θ`**: `S^b_Θ` is nowhere dense in `supp(Θ)`
(closed, `lemma_9_2_7_1`, with dense complement `S^g_Θ`). -/
theorem isNowhereDense_badSet (hΘ : X.IsBranchedEpSubgroupoid Θ) :
    IsNowhereDense ((↑) ⁻¹' X.badSet Θ : Set (supp Θ)) := by
  have h : ((↑) ⁻¹' X.badSet Θ : Set (supp Θ)) = ((↑) ⁻¹' X.goodSet Θ)ᶜ := by
    ext z
    simp only [badSet, mem_preimage, Set.mem_sdiff, mem_compl_iff]
    exact ⟨fun h => h.2, fun h => ⟨z.2, h⟩⟩
  rw [(lemma_9_2_7_1 hΘ).2.isNowhereDense_iff, interior_eq_empty_iff_dense_compl, h,
    compl_compl]
  exact dense_goodSet hΘ

/-- **Lemma 9.2.7 (1), p. 412 (2017: Lemma 9.5 (1), p. 300), the second half**: `S^g_Θ` is
dense and `S^b_Θ` is nowhere dense in `supp(Θ)` (the first half, openness and closedness, is
`lemma_9_2_7_1`). -/
theorem lemma_9_2_7_1_dense (hΘ : X.IsBranchedEpSubgroupoid Θ) :
    Dense ((↑) ⁻¹' X.goodSet Θ : Set (supp Θ)) ∧
      IsNowhereDense ((↑) ⁻¹' X.badSet Θ : Set (supp Θ)) :=
  ⟨dense_goodSet hΘ, isNowhereDense_badSet hΘ⟩

/-- **Lemma 9.2.7 (2), p. 412 (2017: Lemma 9.5 (2), p. 300)**: for a local branching structure
`(Mᵢ)` at `x` whose `Mᵢ` are all `n`-dimensional, and invariance of domain at the points of
`U(x)` (`HasDomainInvarianceAt`), every `Mᵢ` contains a sequence of good points converging to
`x` (the text: for a bad `x`; the statement holds at every `x`).  Proof as in the text: shrink a
neighbourhood of `x` until it meets `Mᵢ ∩ Mⱼ` in all of `Mᵢ` or not at all; a point of `Mᵢ` in
it lies in the interior of each `Σⱼ` it meets, and is good by invariance of domain. -/
theorem lemma_9_2_7_2 {x : Obj} (B : X.LocalBranchingStructure Θ x) {n : ℕ} (hdim : B.IsOfDim n)
    (hDI : ∀ y ∈ B.U, X.PObj.HasDomainInvarianceAt y n) (i : B.ι) :
    ∃ u : ℕ → Obj, (∀ k, u k ∈ B.M i ∧ u k ∈ X.goodSet Θ) ∧ Tendsto u atTop (𝓝 x) := by
  have := MPolyfold.metrizableSpace X.PObj
  suffices hcl : x ∈ closure (B.M i ∩ X.goodSet Θ) by
    obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hcl
    exact ⟨u, hu, hlim⟩
  refine mem_closure_iff_nhds.2 fun O hO => ?_
  obtain ⟨S', hS'S, hS'o, ⟨z, hzS', hzi⟩, hj⟩ :=
    exists_isOpen_subset_inter_eq_empty_or_subset B.M B.isOpen_U_diff_M
      (isOpen_interior.inter B.isOpen_U) inter_subset_right
      ⟨x, ⟨mem_interior_iff_mem_nhds.2 hO, B.mem_U⟩, B.mem_M i⟩
  have hzU : z ∈ B.U := (hS'S hzS').2
  have hsub : ∀ j, z ∈ B.M j → S' ∩ B.M i ⊆ B.M j := fun j hzj => by
    rcases hj j with h | h
    · exact absurd (h ▸ ⟨⟨hzS', hzi⟩, hzj⟩ : z ∈ (∅ : Set Obj)) (notMem_empty z)
    · exact h
  have hV' : ∀ j, ∃ V' ∈ 𝓝 z, z ∈ B.M j → B.M j ∩ V' ⊆ B.M i := fun j => by
    by_cases hzj : z ∈ B.M j
    · obtain ⟨V', hV', hV'sub⟩ := hDI z hzU (B.M i) (B.M j) (hdim i) (hdim j) hzi S'
        (hS'o.mem_nhds hzS') fun w hw => hsub j hzj ⟨hw.2, hw.1⟩
      exact ⟨V', hV', fun _ => hV'sub⟩
    · exact ⟨univ, univ_mem, fun h => absurd h hzj⟩
  choose V' hV'z hV'sub using hV'
  set W := S' ∩ ⋂ j, interior (V' j) with hWdef
  have hWo : IsOpen W := hS'o.inter (isOpen_iInter_of_finite fun j => isOpen_interior)
  have hzW : z ∈ W := ⟨hzS', mem_iInter.2 fun j => mem_interior_iff_mem_nhds.2 (hV'z j)⟩
  have hcover : ∀ j, z ∈ B.M j → W ∩ B.M j = W ∩ B.M i := fun j hzj => by
    refine Subset.antisymm (fun w hw => ⟨hw.1, hV'sub j hzj
      ⟨hw.2, interior_subset (mem_iInter.1 hw.1.2 j)⟩⟩) fun w hw =>
      ⟨hw.1, hsub j hzj ⟨hw.1.1, hw.2⟩⟩
  have hzMU : z ∈ B.MU := mem_iUnion.2 ⟨i, hzi⟩
  have hzsupp : z ∈ supp Θ := by rw [B.MU_eq] at hzMU; exact hzMU.1
  refine ⟨z, interior_subset (hS'S hzS').1, hzi, hzsupp, x, B, hzU, hzMU, W, hWo, hzW,
    fun w hw => (hS'S hw.1).2, fun j j' hzj hzj' => ?_⟩
  rw [hcover j hzj, hcover j' hzj']

/-- **Lemma 9.2.7 (2) over `ℝᵐ`**: no further hypothesis (`hasDomainInvarianceAt_rn`). -/
theorem lemma_9_2_7_2_rn {m : ℕ} {Mor' : Type} [TopologicalSpace Mor'] [T2Space Mor']
    [ParacompactSpace Mor'] {Y : EpGroupoid (Fin m → ℝ) Mor'} (hY : Y.PObj = rnPolyfold m)
    {Θ : (Fin m → ℝ) → ℚ} {x : Fin m → ℝ} (B : Y.LocalBranchingStructure Θ x) {n : ℕ}
    (hdim : B.IsOfDim n) (i : B.ι) :
    ∃ u : ℕ → Fin m → ℝ, (∀ k, u k ∈ B.M i ∧ u k ∈ Y.goodSet Θ) ∧ Tendsto u atTop (𝓝 x) :=
  lemma_9_2_7_2 B hdim (fun y _ => hY ▸ MPolyfold.hasDomainInvarianceAt_rn y n) i

/-! ### Definition 9.2.12: the hypotheses on the `TMᵢ` -/

/-- **`TMᵢ` is closed in `TU(x)`** (a field of `TangentBranchingHyp`, proved): a limit `h` of
vectors of `TMᵢ` lies over `Mᵢ` (closed in `U(x)`), and is fixed by the tangent `Ts` of an
sc⁺-retraction `s` onto `Mᵢ` near `p(h)` (continuity of `Ts`, `TX` Hausdorff). -/
theorem isClosed_tangentSubmanifold {x : Obj} (B : X.LocalBranchingStructure Θ x) (i : B.ι) :
    IsClosed ((↑) ⁻¹' X.tangentSubmanifold (B.M i) : Set (X.PObj.tangentPreimage B.U)) := by
  rw [← closure_subset_iff_isClosed]
  intro h hh
  set T := X.tangentSubmanifold (B.M i) with hTdef
  have hh' : (h : X.PObj.TangentSpace) ∈ closure T :=
    closure_mono (image_preimage_subset _ _) (closure_subtype.1 hh)
  set y := X.PObj.levelVal 1 (X.PObj.tangentProj (h : X.PObj.TangentSpace)) with hydef
  have hyU : y ∈ B.U := h.2
  have hpc := MPolyfold.continuous_levelVal_tangentProj (P := X.PObj)
  have hyM : y ∈ B.M i := by
    by_contra hyM
    have hO : IsOpen ((fun α => X.PObj.levelVal 1 (X.PObj.tangentProj α)) ⁻¹' (B.U \ B.M i)) :=
      (B.isOpen_U_diff_M i).preimage hpc
    obtain ⟨h', hh'O, hh'T⟩ := mem_closure_iff.1 hh' _ hO ⟨hyU, hyM⟩
    exact hh'O.2 (MPolyfold.mem_of_mem_submanifoldTangent hh'T)
  obtain ⟨d, hyd⟩ := MPolyfold.isSmoothSubmanifold_iff.1 (B.isSmoothSubmanifold i) y hyM
  set S := X.PObj.tangentPreimage d.V with hSdef
  have hSo : IsOpen S := MPolyfold.isOpen_tangentPreimage d.isOpen
  have hhS : (h : X.PObj.TangentSpace) ∈ S := hyd
  have hcont : ContinuousOn d.tmap S := MPolyfold.continuousOn_tangentMapOn _
  have hcl : (h : X.PObj.TangentSpace) ∈ closure (T ∩ S) := by
    rw [mem_closure_iff] at hh' ⊢
    intro O hO hhO
    obtain ⟨w, hwO, hwT⟩ := hh' (O ∩ S) (hO.inter hSo) ⟨hhO, hhS⟩
    exact ⟨w, hwO.1, hwT, hwO.2⟩
  have hfix : d.tmap h = h := by
    have : (𝓝[T ∩ S] (h : X.PObj.TangentSpace)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
    have h1 : Tendsto d.tmap (𝓝[T ∩ S] (h : X.PObj.TangentSpace)) (𝓝 (d.tmap h)) :=
      ((hcont _ hhS).mono inter_subset_right).tendsto
    have h2 : Tendsto d.tmap (𝓝[T ∩ S] (h : X.PObj.TangentSpace)) (𝓝 h) := by
      refine (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact (((MPolyfold.mem_submanifoldTangent_iff d hw.2).1 hw.1).2).symm
    exact tendsto_nhds_unique h1 h2
  exact (MPolyfold.mem_submanifoldTangent_iff d hyd).2 ⟨rfl, hfix⟩

/-- **`|supp(TΘ)|` is paracompact** (a field of `TangentBranchingHyp`) when `|X|` is: `|TX|` is
metrizable (`metrizableSpace_tangent_orbitSpace`, Theorem 8.4), hence so is every subspace. -/
theorem paracompactSpace_orbitSupp_tangentTheta (hX : X.HasParacompactOrbitSpace) (Θ : Obj → ℚ) :
    ParacompactSpace (X.tangentEpGroupoid.orbitSupp (X.tangentTheta Θ)) := by
  have := X.metrizableSpace_tangent_orbitSpace hX
  exact paracompactSpace_of_metrizableSpace _

/-- **`TangentBranchingHyp` from its first field**: if `|X|` is paracompact and the `TMᵢ` are
smooth finite-dimensional submanifolds of `TX` (the Part I fact left open: the tangent of an
sc⁺-retraction is an sc⁺-retraction of `TX`), the other fields hold (`TMᵢ ⊆ (TX)_∞` by
Proposition 4.15 (1), closedness, paracompactness). -/
theorem tangentBranchingHyp_of_isSmoothSubmanifold (hX : X.HasParacompactOrbitSpace)
    (hsub : ∀ (x : Obj) (B : X.LocalBranchingStructure Θ x) (i : B.ι),
      X.tangentEpGroupoid.PObj.IsSmoothSubmanifold (X.tangentSubmanifold (B.M i))) :
    X.TangentBranchingHyp Θ :=
  ⟨hsub, fun x B i => (hsub x B i).subset_smoothSet, fun _ B i => isClosed_tangentSubmanifold B i,
    paracompactSpace_orbitSupp_tangentTheta hX Θ⟩

/-- **Definition 9.2.12, p. 418, with the reduced hypothesis**: `TΘ` is a branched
ep⁺-subgroupoid of `T(X, 𝐗)` if `|X|` is paracompact, the tangent sums are independent
(Theorem 9.2.1) and the `TMᵢ` are smooth submanifolds of `TX`. -/
theorem isBranchedEpSubgroupoid_tangentTheta_of_isSmoothSubmanifold
    (hΘ : X.IsBranchedEpSubgroupoid Θ) (hind : X.HasIndependentTangentSums Θ)
    (hX : X.HasParacompactOrbitSpace)
    (hsub : ∀ (x : Obj) (B : X.LocalBranchingStructure Θ x) (i : B.ι),
      X.tangentEpGroupoid.PObj.IsSmoothSubmanifold (X.tangentSubmanifold (B.M i))) :
    X.tangentEpGroupoid.IsBranchedEpSubgroupoid (X.tangentTheta Θ) :=
  X.isBranchedEpSubgroupoid_tangentTheta hΘ hind
    (tangentBranchingHyp_of_isSmoothSubmanifold hX hsub)

end EpGroupoid

namespace EpGroupoid.Remark913Hyp

variable {β₁ β₂ : ℝ → ℝ} (h : Remark913Hyp β₁ β₂)
include h

/-- **The origin is a bad point** of the `Θ` of Remark 9.1.3 (b): `Θ(0) = 2`, while `Θ = 1` at
the points `(s, β₁(s))`, `s > 0`, of `supp(Θ)` arbitrarily close to `0`. -/
theorem zero_mem_badSet :
    (0 : Fin 2 → ℝ) ∈ (trivial (rnPolyfold 2)).badSet (thetaGraphs β₁ β₂) := by
  have hΘ := (remark_9_1_3_b h).1
  have h10 : β₁ 0 = 0 := h.eq_zero₁ 0 le_rfl
  have h20 : β₂ 0 = 0 := h.eq_zero₂ 0 le_rfl
  have hΘ0 : thetaGraphs β₁ β₂ 0 = 2 := by
    rw [thetaGraphs_apply]
    change ((if (0 : ℝ) = β₁ 0 then 1 else 0) + if (0 : ℝ) = β₂ 0 then 1 else 0 : ℚ) = 2
    rw [if_pos h10.symm, if_pos h20.symm]
    norm_num
  refine ⟨show (0 : ℚ) < thetaGraphs β₁ β₂ 0 by rw [hΘ0]; norm_num, fun hg => ?_⟩
  obtain ⟨-, V, hV, hc⟩ := (mem_goodSet_iff hΘ).1 hg
  obtain ⟨O, hOV, hO, h0O⟩ := mem_nhds_iff.1 hV
  obtain ⟨s, hs, hsO, -⟩ := exists_curve2_mem h.contDiff₁.continuous h10 hO h0O
  have hval : thetaGraphs β₁ β₂ (curve2 β₁ s) = 1 := by
    rw [thetaGraphs_apply]
    change ((if β₁ s = β₁ s then 1 else 0) + if β₁ s = β₂ s then 1 else 0 : ℚ) = 1
    rw [if_pos rfl, if_neg (by rw [h.eq_zero₂ s hs.le]; exact (h.pos₁ s hs).ne')]
    norm_num
  have := hc _ (hOV hsO) (show (0 : ℚ) < thetaGraphs β₁ β₂ (curve2 β₁ s) by rw [hval]; norm_num)
  rw [hval, hΘ0] at this
  norm_num at this

/-- **A nontrivial instance of Lemma 9.2.7 (2)**: at the bad point `0` of Remark 9.1.3 (b), each
graph `Mᵢ` of the local branching structure contains good points converging to `0`. -/
theorem exists_seq_goodSet_structureβ (i : (h.structureβ 0).ι) :
    ∃ u : ℕ → Fin 2 → ℝ, (∀ k, u k ∈ (h.structureβ 0).M i ∧
      u k ∈ (trivial (rnPolyfold 2)).goodSet (thetaGraphs β₁ β₂)) ∧ Tendsto u atTop (𝓝 0) :=
  lemma_9_2_7_2_rn rfl (h.structureβ 0) (h.structureβ_isOfDim 0) i

end EpGroupoid.Remark913Hyp

end Polyfold
