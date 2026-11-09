import Polyfold.Chapter9.GeneralLevelZero
import Polyfold.Chapter9.DimDecompositionExists

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9: **Proposition 9.1.12** (p. 408; new in the 2021 edition), **Theorem 9.2.1**
(p. 409; 2017: Theorem 9.1, p. 298), **Lemma 9.2.7(2)** (p. 412; 2017: Lemma 9.5(2), p. 300),
**Lemma 9.6.4** (p. 455) and **Proposition 9.6.5** (p. 456), **Proposition 9.1.11** (p. 407) and
**Lemma 9.3.4** (p. 423; 2017: Lemma 9.10), for every ep-groupoid, from the level-`0` facts of
`GeneralLevelZero.lean`.  Numbers and pages are the 2021 text's.

# Chapter 9 without the level-`0` hypotheses

## The text, paraphrased

(p. 455, "as in the discussion of good points") The proofs of Lemma 9.6.4 and of the
independence on p. 457 count the weights of the sheets through slices transverse to a common
tangent space; the slices come from the graph representation of Lemmas 9.2.9–9.2.11
(pp. 414–417), which the text proves in a chart for every M-polyfold.

## What is formalized

* **Slices at every point** (`exists_slice_of_classGraphChart`, `exists_generic_slice_general`,
  `hasTangentSlicesAt`): the slice lemmas of `AppendixSlices.lean` and `TangentSlicesBasic.lean`
  with the admissible directions chosen per tangent space (`HasClassGraphChartAt`, which holds
  everywhere by `hasClassGraphChartAt`).  `hasTangentSlicesAt` makes the hypothesis
  `HasTangentSlicesAt` of `Tangent.lean` unnecessary.
* **`TopMultiplicity` for every M-polyfold** (`sum_class_eq`, `topMultiplicityAt`,
  `topMultiplicity`): this makes the hypotheses `TopMultiplicity` / `TopMultiplicityAt` of
  `Appendix.lean` and `AppendixSlices.lean` unnecessary.
* **Proposition 9.1.12 for every ep-groupoid** (`proposition_9_1_12`,
  `LocalBranchingStructure.dimPartsAgreeNear`), replacing `proposition_9_1_12_of_topMultiplicity`
  and `proposition_9_1_12_of_hasGraphChartAt`.
* **Lemma 9.6.4, Proposition 9.6.5 and the formula of p. 457 for every ep-groupoid**
  (`lemma_9_6_4_general`, `isTopBadPoint_iff_general`, `proposition_9_6_5_general`,
  `sum_class_eq`, `dimPart_topDim_eq`).
* **Theorem 9.2.1 (1), the independence of `∑ σᵢ · T_xMᵢ`, for every `Θ`**
  (`hasIndependentTangentSums`), replacing the `_of_hasGraphChartAt` and
  `_of_hasLocallyConstantDimAt` versions.
* **Lemma 9.2.7(2) without invariance of domain** (`lemma_9_2_7_2_general`; the hypothesis
  `HasDomainInvarianceAt` holds by `hasDomainInvarianceAt`).
* **Proposition 9.1.11** (in the reading of its proof, `Proposition_9_1_11_local`): existence and
  uniqueness of the local dimensional decomposition for every branched ep⁺-subgroupoid
  (`existsUnique_localDimDecomposition_general`, `proposition_9_1_11_unique`), local finiteness
  at the points of `supp(Θ)` (`dimComponent_locallyFinite_of_mem_general`), and the full
  statement under a bound on the dimensions (`proposition_9_1_11_local_of_le`).
* **Lemma 9.3.4 without the level-`1` continuity hypothesis** (`lemma_9_3_4_of_hasGraphBallAt'`),
  and **without hypotheses on the interior `X ∖ ∂X`** (`lemma_9_3_4_of_degIndex_eq_zero`: `supp(Θ)`
  of degeneracy index `0`, e.g. M-polyfolds without boundary).

## What the text leaves implicit, and the choices made

* The project's earlier hypothesis `HasGraphChartAt` (one cone `K` for all submanifolds through
  `x`) was stronger than the text needs: the slice arguments only ever use the cone of the class
  at hand, so they are restated with one cone per tangent space.  The proofs are those of
  `AppendixSlices.lean`, with this one change.
* **Local finiteness of `(Θ_k)` off `supp(Θ)`** still takes a bound on the dimensions of the
  submanifolds (`proposition_9_1_11_local_of_le`): at a point outside `supp(Θ)` no local
  branching structure is given, and our proof uses the bound there; whether it can be dropped is
  not settled here.
* **Lemma 9.3.4 at boundary points**: the project's earlier hypothesis, the ball form of the
  graph representation (`HasGraphBallAt`) at the points of `supp(Θ)`, was stronger than the text
  needs.  It is proved here at interior points (`hasGraphBallAt_of_mem_interior`); the
  good-point input of `OrientationUniqueness.lean` is derived from the one-sided (cone) form at
  every point in `GeneralBoundaryPoints.lean`.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Module

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-! ### Slices with one cone per tangent space -/

/-- **Tangent slices for a finite family of sheets, one admissible cone per tangent space** (the
slice form of 2021 Proposition 9.2.8, p. 413): as `exists_slice_of_isGraphChartAt`, with the
admissible directions `K(T_xA_k)` depending on the tangent space.  Only the cone of the class of
`A_{k₀}` is used. -/
theorem exists_slice_of_classGraphChart {x : X} {φ : MChart X} (hφ : P.IsChart φ)
    (hxφ : x ∈ φ.source) {K : Set (φ.model.E 0) → Set (φ.model.E 0)} {κ : Type*} [Finite κ]
    (A : κ → Set X)
    (hA : ∀ k, P.IsSmoothSubmanifold (A k)) (hx : ∀ k, x ∈ A k)
    (hg : ∀ k, P.IsGraphChartAt hφ (K (P.chartTangent hφ (A k) x)) (A k) x) (k₀ : κ)
    (hnle : ∀ k, P.chartTangent hφ (A k) x ≠ P.chartTangent hφ (A k₀) x →
      ¬ P.chartTangent hφ (A k₀) x ⊆ P.chartTangent hφ (A k) x)
    {W : Set X} (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ F ⊆ W, ∀ k,
      (P.chartTangent hφ (A k) x = P.chartTangent hφ (A k₀) x → ∃! y, y ∈ F ∩ A k) ∧
      (P.chartTangent hφ (A k) x ≠ P.chartTangent hφ (A k₀) x → F ∩ A k = ∅) := by
  classical
  choose N hN hfin using fun k => exists_submodule_chartTangent hφ (hA k) (hx k) hxφ
  have hclass : ∀ k, P.chartTangent hφ (A k) x = P.chartTangent hφ (A k₀) x ↔
      N k = N k₀ := fun k => by
    rw [← hN k, ← hN k₀, SetLike.coe_set_eq]
  have hnle' : ∀ k, N k ≠ N k₀ → ¬ N k₀ ≤ N k := fun k hk hle => by
    refine hnle k (fun h => hk ((hclass k).1 h)) ?_
    rw [← hN k, ← hN k₀]
    exact SetLike.coe_subset_coe.2 hle
  have hclosed : ∀ k, IsClosed (N k : Set (φ.model.E 0)) := fun k => by
    have := hfin k
    exact Submodule.closed_of_finiteDimensional _
  -- the vector `h₀`
  obtain ⟨h₁, hh₁, r, hr, hK⟩ := (hg k₀).exists_ball
  rw [← hN k₀] at hh₁
  obtain ⟨h₀, hh₀N, hh₀r, hh₀S⟩ := exists_mem_ball_forall_not_mem (N := N k₀)
    (ι := {k // N k ≠ N k₀}) (fun k => N k.1) (fun k => hclosed k.1) (fun k => hnle' k.1 k.2)
    hh₁ hr
  have hh₀T : h₀ ∈ P.chartTangent hφ (A k₀) x := by rw [← hN k₀]; exact hh₀N
  have hh₀K : h₀ ∈ K (P.chartTangent hφ (A k₀) x) := hK h₀ hh₀T hh₀r
  -- the projection `Q` onto `L`
  have := hfin k₀
  obtain ⟨Q', hQ'⟩ := Submodule.ClosedComplemented.of_finiteDimensional (N k₀)
  set Q : φ.model.E 0 →L[ℝ] φ.model.E 0 := (N k₀).subtypeL.comp Q' with hQdef
  have hT : ∀ k, N k = N k₀ → P.chartTangent hφ (A k) x = P.chartTangent hφ (A k₀) x :=
    fun k hk => by rw [← hN k, ← hN k₀, hk]
  have hQT : ∀ k, N k = N k₀ → ∀ v, Q v ∈ P.chartTangent hφ (A k) x := fun k hk v => by
    rw [← hN k, hk]; exact (Q' v).2
  have hQid : ∀ k, N k = N k₀ → ∀ v ∈ P.chartTangent hφ (A k) x, Q v = v := fun k hk v hv => by
    rw [← hN k, hk] at hv
    exact congrArg Subtype.val (hQ' ⟨v, hv⟩)
  set c := ‖ContinuousLinearMap.id ℝ (φ.model.E 0) - Q‖ with hcdef
  have hc : 0 ≤ c := norm_nonneg _
  -- the distances of `h₀` to the other tangent spaces
  have hrad : ∀ k, N k ≠ N k₀ → ∃ ρ > 0, ∀ v ∈ P.chartTangent hφ (A k) x, ρ ≤ ‖h₀ - v‖ :=
    fun k hk => by
      have hmem : h₀ ∈ (N k : Set (φ.model.E 0))ᶜ := hh₀S ⟨k, hk⟩
      obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 (hclosed k).isOpen_compl h₀ hmem
      refine ⟨ρ, hρ, fun v hv => ?_⟩
      by_contra hlt
      push Not at hlt
      rw [← hN k] at hv
      exact hball (by rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]; exact hlt) hv
  choose! ρ hρ hρv using hrad
  -- the tube radius `ε`
  have hεev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ 1 ∧ ∀ k, N k ≠ N k₀ → ε ≤ ρ k / 3 := by
    refine Filter.Eventually.and ?_ (Filter.eventually_all.2 fun k => ?_)
    · exact ((eventually_lt_nhds one_pos).mono fun _ h => h.le).filter_mono nhdsWithin_le_nhds
    · by_cases hk : N k ≠ N k₀
      · exact ((eventually_lt_nhds (by linarith [hρ k hk] : (0 : ℝ) < ρ k / 3)).mono
          fun _ h _ => h.le).filter_mono nhdsWithin_le_nhds
      · exact Filter.Eventually.of_forall fun _ h => (hk h).elim
  obtain ⟨ε, ⟨hε1, hερ⟩, hε0⟩ := (hεev.and self_mem_nhdsWithin).exists
  have hε0 : (0 : ℝ) < ε := hε0
  -- the constants of the approximation
  set η : ℝ := 1 / (2 * (c + 1)) with hηdef
  have hη : 0 < η := by positivity
  have hηc : η * c < 1 := by
    rw [hηdef, div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
    linarith
  choose δ₁ hδ₁ happ₁ using fun k => (hg k).approx η hη
  have happ₂ : ∀ k, N k ≠ N k₀ → ∃ δ > 0, ∀ a ∈ A k ∩ φ.source, ∀ b ∈ A k ∩ φ.source,
      ‖φ a - φ x‖ < δ → ‖φ b - φ x‖ < δ → ∃ v ∈ P.chartTangent hφ (A k) x,
        ‖(φ a - φ b) - v‖ ≤ ρ k / (3 * (‖h₀‖ + 1)) * ‖φ a - φ b‖ := fun k hk =>
    (hg k).approx _ (by have := hρ k hk; positivity)
  choose! δ₂ hδ₂ happ₂ using happ₂
  have hgr : ∀ k, N k = N k₀ → ∃ t₀ > 0, ∀ t, 0 < t → t < t₀ → ∃ a ∈ A k ∩ φ.source,
      Q (φ a - φ x) = t • h₀ ∧ ‖(φ a - φ x) - t • h₀‖ ≤ ε / 2 * t := fun k hk =>
    (hg k).graph Q (hQT k hk) (hQid k hk) h₀ (by rw [hT k hk]; exact hh₀T)
      (by rw [hT k hk]; exact hh₀K) (ε / 2)
      (by positivity)
  choose! t₀ ht₀ hgr using hgr
  obtain ⟨ρW, hρW, hW'⟩ := exists_pos_forall_mem_of_mem_nhds hxφ (hW.mem_nhds hxW)
  -- the parameter `t`
  have htev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ k, N k = N k₀ → t < t₀ k) ∧
      (∀ k, t * (‖h₀‖ + 1) < δ₁ k) ∧ (∀ k, N k ≠ N k₀ → t * (‖h₀‖ + 1) < δ₂ k) ∧
      t * (‖h₀‖ + 1) < ρW := by
    refine ((Filter.eventually_all.2 fun k => ?_).and ((Filter.eventually_all.2 fun k =>
      eventually_mul_lt (hδ₁ k)).and ((Filter.eventually_all.2 fun k => ?_).and
        (eventually_mul_lt hρW)))).mono fun t ht => ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2⟩
    · by_cases hk : N k = N k₀
      · exact ((eventually_lt_nhds (ht₀ k hk)).mono fun _ h _ => h).filter_mono
          nhdsWithin_le_nhds
      · exact Filter.Eventually.of_forall fun _ h => (hk h).elim
    · by_cases hk : N k ≠ N k₀
      · exact (eventually_mul_lt (hδ₂ k hk)).mono fun _ h _ => h
      · exact Filter.Eventually.of_forall fun _ h => (hk h).elim
  obtain ⟨t, ⟨ht₀', htδ₁, htδ₂, htW⟩, ht0⟩ := (htev.and self_mem_nhdsWithin).exists
  have ht0 : (0 : ℝ) < t := ht0
  -- the slice
  set F : Set X := {y | y ∈ W ∧ y ∈ φ.source ∧ Q (φ y - φ x) = t • h₀ ∧
    ‖(φ y - φ x) - t • h₀‖ < ε * t} with hFdef
  have hFnorm : ∀ y, ‖(φ y - φ x) - t • h₀‖ < ε * t → ‖φ y - φ x‖ < t * (‖h₀‖ + 1) := by
    intro y hy
    calc ‖φ y - φ x‖ = ‖((φ y - φ x) - t • h₀) + t • h₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖(φ y - φ x) - t • h₀‖ + ‖t • h₀‖ := norm_add_le _ _
      _ < ε * t + t * ‖h₀‖ := by
          rw [norm_smul, Real.norm_of_nonneg ht0.le]; linarith
      _ ≤ t * (‖h₀‖ + 1) := by nlinarith
  refine ⟨F, fun y hy => hy.1, fun k => ⟨fun hk => ?_, fun hk => ?_⟩⟩
  · -- `T_xA_k = L`: exactly one point
    have hk' : N k = N k₀ := (hclass k).1 hk
    obtain ⟨a, haA, haQ, hanorm⟩ := hgr k hk' t ht0 (ht₀' k hk')
    have ha_lt : ‖(φ a - φ x) - t • h₀‖ < ε * t := by
      have : ε / 2 * t < ε * t := by nlinarith
      linarith
    have haF : a ∈ F := ⟨hW' a haA.2 ((hFnorm a ha_lt).trans htW), haA.2, haQ, ha_lt⟩
    refine ⟨a, ⟨haF, haA.1⟩, fun b hb => ?_⟩
    have hbF : b ∈ F := hb.1
    obtain ⟨v, hv, hvb⟩ := happ₁ k b ⟨hb.2, hbF.2.1⟩ a haA
      ((hFnorm b hbF.2.2.2).trans (htδ₁ k)) ((hFnorm a ha_lt).trans (htδ₁ k))
    have hQba : Q (φ b - φ a) = 0 := by
      have : φ b - φ a = (φ b - φ x) - (φ a - φ x) := by abel
      rw [this, map_sub, hbF.2.2.1, haQ, sub_self]
    have h0 := eq_zero_of_proj_eq_zero (hQid k hk') hQba hv hηc hvb
    exact φ.toPartialEquiv.injOn hbF.2.1 haA.2 (sub_eq_zero.1 h0)
  · -- `T_xA_k ≠ L`: no point
    have hk' : N k ≠ N k₀ := fun h => hk ((hclass k).2 h)
    refine eq_empty_of_forall_notMem fun a ha => ?_
    have haF : a ∈ F := ha.1
    have hnorm := hFnorm a haF.2.2.2
    have hxA : x ∈ A k ∩ φ.source := ⟨hx k, hxφ⟩
    obtain ⟨v, hv, hva⟩ := happ₂ k hk' a ⟨ha.2, haF.2.1⟩ x hxA (hnorm.trans (htδ₂ k hk'))
      (by rw [sub_self, norm_zero]; exact hδ₂ k hk')
    have hρk := hρ k hk'
    have h1 : ‖(φ a - φ x) - v‖ ≤ t * (ρ k / 3) := by
      calc ‖(φ a - φ x) - v‖ ≤ ρ k / (3 * (‖h₀‖ + 1)) * ‖φ a - φ x‖ := hva
        _ ≤ ρ k / (3 * (‖h₀‖ + 1)) * (t * (‖h₀‖ + 1)) :=
            mul_le_mul_of_nonneg_left hnorm.le (by positivity)
        _ = t * (ρ k / 3) := by field_simp
    have h2 : ‖t • h₀ - v‖ < t * (2 * ρ k / 3) := by
      calc ‖t • h₀ - v‖ = ‖((φ a - φ x) - v) - ((φ a - φ x) - t • h₀)‖ := by
            congr 1; abel
        _ ≤ ‖(φ a - φ x) - v‖ + ‖(φ a - φ x) - t • h₀‖ := norm_sub_le _ _
        _ < t * (ρ k / 3) + ε * t := by linarith [haF.2.2.2]
        _ ≤ t * (2 * ρ k / 3) := by nlinarith [hερ k hk']
    have hv' : t⁻¹ • v ∈ P.chartTangent hφ (A k) x := by
      rw [← hN k] at hv ⊢; exact (N k).smul_mem _ hv
    have h3 := hρv k hk' _ hv'
    have h4 : ‖h₀ - t⁻¹ • v‖ = t⁻¹ * ‖t • h₀ - v‖ := by
      have : h₀ - t⁻¹ • v = t⁻¹ • (t • h₀ - v) := by
        rw [smul_sub, smul_smul, inv_mul_cancel₀ ht0.ne', one_smul]
      rw [this, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht0.le)]
    rw [h4] at h3
    have h5 : t⁻¹ * ‖t • h₀ - v‖ < 2 * ρ k / 3 := by
      rw [inv_mul_lt_iff₀ ht0]; linarith
    linarith


/-- **Generic tangent slices at every point** (for 2021 Proposition 9.6.5, p. 456): as
`exists_generic_slice`, without the hypothesis `HasGraphChartAt` (the graph representation holds
everywhere with one cone per tangent space, `hasClassGraphChartAt`). -/
theorem exists_generic_slice_general {x : X} {k : ℕ} {κ ν : Type*}
    [Finite κ] [Finite ν] (A : κ → Set X) (hA : ∀ j, P.IsSubmanifoldOfDim (A j) k)
    (hx : ∀ j, x ∈ A j) (j₀ : κ) {O : Set X} (hO : IsOpen O) (hxO : x ∈ O)
    (L : ν → Set X) (dL : ν → ℕ)
    (hL : ∀ l, P.IsSubmanifoldOfDim (L l) (dL l) ∧ dL l < k ∧ IsOpen (O \ L l))
    {W : Set X} (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ F ⊆ W ∩ O, (∀ y ∈ F, ∀ l, y ∉ L l) ∧ ∀ j,
      (P.submanifoldTangent (A j) x = P.submanifoldTangent (A j₀) x → ∃! y, y ∈ F ∩ A j) ∧
      (P.submanifoldTangent (A j) x ≠ P.submanifoldTangent (A j₀) x → F ∩ A j = ∅) := by
  classical
  obtain ⟨φ, hφ, hxφ, K, hGA⟩ := hasClassGraphChartAt (P := P) x
  let A' : κ ⊕ {l // x ∈ L l} → Set X := Sum.elim A (fun l => L l.1)
  let T : ν → Set X := fun l => if x ∈ L l then univ else O \ L l
  have hTo : ∀ l, IsOpen (T l) := fun l => by
    simp only [T]; split_ifs; exacts [isOpen_univ, (hL l).2.2]
  have hxT : ∀ l, x ∈ T l := fun l => by
    simp only [T]; split_ifs with h; exacts [mem_univ x, ⟨hxO, h⟩]
  have hW' : IsOpen (W ∩ O ∩ ⋂ l, T l) := (hW.inter hO).inter (isOpen_iInter_of_finite hTo)
  have hxW' : x ∈ W ∩ O ∩ ⋂ l, T l := ⟨⟨hxW, hxO⟩, mem_iInter.2 hxT⟩
  have hdim : ∀ k', ∃ d ≤ k, P.IsSubmanifoldOfDim (A' k') d := fun k' => by
    cases k' with
    | inl j => exact ⟨k, le_rfl, hA j⟩
    | inr l => exact ⟨dL l.1, (hL l.1).2.1.le, (hL l.1).1⟩
  have hA'x : ∀ k', x ∈ A' k' := fun k' => by
    cases k' with
    | inl j => exact hx j
    | inr l => exact l.2
  have hg : ∀ k', P.IsGraphChartAt hφ (K (P.chartTangent hφ (A' k') x)) (A' k') x :=
    fun k' => by
      obtain ⟨d, -, hd⟩ := hdim k'
      exact hGA _ hd.1 (hA'x k')
  have hnle : ∀ k', P.chartTangent hφ (A' k') x ≠ P.chartTangent hφ (A' (Sum.inl j₀)) x →
      ¬ P.chartTangent hφ (A' (Sum.inl j₀)) x ⊆ P.chartTangent hφ (A' k') x := fun k' hne => by
    obtain ⟨d, hdk, hd⟩ := hdim k'
    exact not_chartTangent_subset hφ hxφ (hA j₀).1 ((hA j₀).2 x (hx j₀)) hd.1
      (hd.2 x (hA'x k')) hdk hne
  obtain ⟨F, hFW, hF⟩ := exists_slice_of_classGraphChart hφ hxφ A' (fun k' => by
    obtain ⟨d, -, hd⟩ := hdim k'; exact hd.1) hA'x hg (Sum.inl j₀) hnle hW' hxW'
  refine ⟨F, fun y hy => (hFW hy).1, fun y hy l => ?_, fun j => ⟨fun hj => ?_, fun hj => ?_⟩⟩
  · by_cases hxl : x ∈ L l
    · intro hyl
      have hne : P.chartTangent hφ (A' (Sum.inr ⟨l, hxl⟩)) x ≠
          P.chartTangent hφ (A' (Sum.inl j₀)) x := fun h => by
        have := HasDimAt.eq_of_chartTangent_eq hφ hxφ (hL l).1.1 ((hL l).1.2 x hxl) (hA j₀).1
          ((hA j₀).2 x (hx j₀)) h
        exact absurd (hL l).2.1 (by omega)
      have h1 : y ∈ F ∩ A' (Sum.inr ⟨l, hxl⟩) := ⟨hy, hyl⟩
      rw [(hF (Sum.inr ⟨l, hxl⟩)).2 hne] at h1
      exact h1
    · have hyT : y ∈ T l := mem_iInter.1 (hFW hy).2 l
      simp only [T, if_neg hxl] at hyT
      exact hyT.2
  · exact (hF (Sum.inl j)).1 ((chartTangent_eq_iff hφ hxφ).2 hj)
  · exact (hF (Sum.inl j)).2 fun h => hj ((chartTangent_eq_iff hφ hxφ).1 h)

open scoped Classical in
/-- **The class weights of two families agree** (2021 p. 457), at every point: as
`sum_class_eq_of_hasGraphChartAt`, without its hypothesis. -/
theorem sum_class_eq {x : X} {k : ℕ} {O : Set X}
    (hO : IsOpen O) (hxO : x ∈ O) {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Finite ν]
    (M : ι → Set X) (σ : ι → ℚ) (N : κ → Set X) (τ : κ → ℚ) (L : ν → Set X) (dL : ν → ℕ)
    (hM : ∀ i, P.IsSubmanifoldOfDim (M i) k ∧ x ∈ M i)
    (hN : ∀ j, P.IsSubmanifoldOfDim (N j) k ∧ x ∈ N j)
    (hL : ∀ l, P.IsSubmanifoldOfDim (L l) (dL l) ∧ dL l < k ∧ IsOpen (O \ L l))
    (hagree : ∀ y ∈ O, (∀ l, y ∉ L l) → ∑ i with y ∈ M i, σ i = ∑ j with y ∈ N j, τ j)
    (T : Set P.TangentSpace) :
    (∑ i, if P.submanifoldTangent (M i) x = T then σ i else 0) =
      ∑ j, if P.submanifoldTangent (N j) x = T then τ j else 0 := by
  let A : ι ⊕ κ → Set X := Sum.elim M N
  by_cases hT : ∃ k₀, P.submanifoldTangent (A k₀) x = T
  swap
  · push Not at hT
    have h1 : ∀ i, P.submanifoldTangent (M i) x ≠ T := fun i => hT (Sum.inl i)
    have h2 : ∀ j, P.submanifoldTangent (N j) x ≠ T := fun j => hT (Sum.inr j)
    simp only [h1, h2, if_false, Finset.sum_const_zero]
  obtain ⟨k₀, hk₀⟩ := hT
  have hAd : ∀ k', P.IsSubmanifoldOfDim (A k') k := fun k' => by
    cases k' with
    | inl i => exact (hM i).1
    | inr j => exact (hN j).1
  have hAx : ∀ k', x ∈ A k' := fun k' => by
    cases k' with
    | inl i => exact (hM i).2
    | inr j => exact (hN j).2
  obtain ⟨F, hFWO, hFL, hF⟩ := exists_generic_slice_general A hAd hAx k₀ hO hxO L dL hL hO hxO
  have hgood : ∀ k', P.submanifoldTangent (A k') x = T →
      ∃ y, y ∈ F ∩ A k' ∧ ∀ y', y' ∈ F ∩ A k' → y' = y :=
    fun k' hk' => (hF k').1 (hk'.trans hk₀.symm)
  have hbad : ∀ k', P.submanifoldTangent (A k') x ≠ T → F ∩ A k' = ∅ :=
    fun k' hk' => (hF k').2 fun h => hk' (h.trans hk₀)
  have : Nonempty X := ⟨x⟩
  choose! pt hpt hpt_uniq using hgood
  let S : Finset X :=
    (Finset.univ.filter fun k' => P.submanifoldTangent (A k') x = T).image pt
  have hSF : ∀ y ∈ S, y ∈ F := fun y hy => by
    obtain ⟨k', hk', rfl⟩ := Finset.mem_image.1 hy
    exact (hpt k' (Finset.mem_filter.1 hk').2).1
  have hcount : ∀ k' (c : ℚ), (∑ y ∈ S, if y ∈ A k' then c else 0) =
      if P.submanifoldTangent (A k') x = T then c else 0 := fun k' c => by
    by_cases hk' : P.submanifoldTangent (A k') x = T
    · rw [if_pos hk', Finset.sum_eq_single (pt k')]
      · exact if_pos (hpt k' hk').2
      · intro y hyS hne
        exact if_neg fun hyA => hne (hpt_uniq k' hk' y ⟨hSF y hyS, hyA⟩)
      · intro hn
        exact (hn (Finset.mem_image_of_mem pt
          (Finset.mem_filter.2 ⟨Finset.mem_univ k', hk'⟩))).elim
    · rw [if_neg hk']
      refine Finset.sum_eq_zero fun y hy => if_neg fun hyA => ?_
      have h1 : y ∈ F ∩ A k' := ⟨hSF y hy, hyA⟩
      rw [hbad k' hk'] at h1
      exact h1
  have hB1 : (∑ i, if P.submanifoldTangent (M i) x = T then σ i else 0) =
      ∑ y ∈ S, ∑ i with y ∈ M i, σ i := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => (hcount (Sum.inl i) (σ i)).symm
  have hB2 : (∑ j, if P.submanifoldTangent (N j) x = T then τ j else 0) =
      ∑ y ∈ S, ∑ j with y ∈ N j, τ j := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => (hcount (Sum.inr j) (τ j)).symm
  rw [hB1, hB2]
  exact Finset.sum_congr rfl fun y hy => hagree y (hFWO (hSF y hy)).2 (hFL y (hSF y hy))

open scoped Classical in
/-- **`TopMultiplicity` at every point of every M-polyfold** (the step of 2021 Lemma 9.6.4,
p. 455, "as in the discussion of good points"). -/
theorem topMultiplicityAt (x : X) (k : ℕ) :
    P.TopMultiplicityAt x k := by
  intro O hO hxO ι κ ν _ _ _ M σ N τ L dL hM hN hL hagree
  have hclass := sum_class_eq hO hxO M σ N τ L dL
    (fun i => ⟨(hM i).1, (hM i).2.1⟩) (fun j => ⟨(hN j).1, (hN j).2.1⟩) hL hagree
  set Ts : Finset (Set P.TangentSpace) :=
    Finset.univ.image (fun i => P.submanifoldTangent (M i) x) ∪
      Finset.univ.image (fun j => P.submanifoldTangent (N j) x)
  rw [sum_eq_sum_classes (fun i => P.submanifoldTangent (M i) x) σ Ts
      (fun i => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))),
    sum_eq_sum_classes (fun j => P.submanifoldTangent (N j) x) τ Ts
      (fun j => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))]
  exact Finset.sum_congr rfl fun T _ => hclass T

/-- **`MPolyfold.TopMultiplicity` holds for every M-polyfold and every `k`**: the hypothesis of
`proposition_9_1_12_of_topMultiplicity`, `lemma_9_6_4` and `dimPartsAgreeNear_of_topMultiplicity`
is now unnecessary. -/
theorem topMultiplicity (k : ℕ) : P.TopMultiplicity k := fun x => topMultiplicityAt x k

/-- **Tangent slices at every point of every M-polyfold** (2021 Proposition 9.2.8, p. 413, slice
form; Lemmas 9.2.9–9.2.11): the hypothesis `HasTangentSlicesAt` of the fibre count of
`Tangent.lean` is now unnecessary. -/
theorem hasTangentSlicesAt (x : X) (n : ℕ) : P.HasTangentSlicesAt x n := by
  intro κ _ A hA hx k₀ W hW hxW
  obtain ⟨φ, hφ, hxφ, K, hGA⟩ := hasClassGraphChartAt (P := P) x
  obtain ⟨F, hFW, hF⟩ := exists_slice_of_classGraphChart hφ hxφ A (fun k => (hA k).1) hx
    (fun k => hGA _ (hA k).1 (hx k)) k₀
    (fun k hne => not_chartTangent_subset hφ hxφ (hA k₀).1 ((hA k₀).2 x (hx k₀)) (hA k).1
      ((hA k).2 x (hx k)) le_rfl hne) hW hxW
  exact ⟨F, hFW, fun k => ⟨fun hk => (hF k).1 ((chartTangent_eq_iff hφ hxφ).2 hk),
    fun hk => (hF k).2 fun h => hk ((chartTangent_eq_iff hφ hxφ).1 h)⟩⟩

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ}

/-! ### Proposition 9.1.12, Lemma 9.6.4, Proposition 9.6.5 -/

/-- **2021 Proposition 9.1.12, p. 408 (new in the 2021 edition; proof §9.6.1, pp. 452–457), for
every ep-groupoid**: the dimensional decompositions of any two labelled local branching
structures of any `Θ` agree near the base point (`proposition_9_1_12_of_topMultiplicity` with
`MPolyfold.topMultiplicity`). -/
theorem proposition_9_1_12 : X.Proposition_9_1_12 :=
  proposition_9_1_12_of_topMultiplicity fun k => MPolyfold.topMultiplicity k

namespace LocalBranchingStructure

variable {x : Obj}

/-- **2021 Proposition 9.1.12 locally**, for every ep-groupoid: two labelled local branching
structures at `x` have the same dimensional parts near `x`; no branched hypothesis on `Θ`. -/
theorem dimPartsAgreeNear (B B' : X.LocalBranchingStructure Θ x) {dim : B.ι → ℕ}
    {dim' : B'.ι → ℕ} (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i))
    (hdim' : ∀ j, X.PObj.IsSubmanifoldOfDim (B'.M j) (dim' j)) :
    DimPartsAgreeNear B B' dim dim' :=
  dimPartsAgreeNear_of_topMultiplicity (fun k => MPolyfold.topMultiplicity k) B B' hdim hdim'

open scoped Classical in
/-- **2021 Lemma 9.6.4, p. 455 (new in the 2021 edition), for every ep-groupoid**: a point of
`U ∩ U'` is top-good for one labelled local branching structure iff it is for the other. -/
theorem lemma_9_6_4_general {B B' : X.LocalBranchingStructure Θ x} {dim : B.ι → ℕ}
    {dim' : B'.ι → ℕ} (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i))
    (hdim' : ∀ j, X.PObj.IsSubmanifoldOfDim (B'.M j) (dim' j)) {y : Obj} (hyU : y ∈ B.U)
    (hyU' : y ∈ B'.U) : B.IsTopGoodPoint dim y ↔ B'.IsTopGoodPoint dim' y :=
  lemma_9_6_4 (MPolyfold.topMultiplicity _) hdim hdim' hyU hyU'

open scoped Classical in
/-- **2021 Lemma 9.6.4, p. 455, for top-bad points**, for every ep-groupoid. -/
theorem isTopBadPoint_iff_general {B B' : X.LocalBranchingStructure Θ x} {dim : B.ι → ℕ}
    {dim' : B'.ι → ℕ} (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i))
    (hdim' : ∀ j, X.PObj.IsSubmanifoldOfDim (B'.M j) (dim' j)) {y : Obj} (hyU : y ∈ B.U)
    (hyU' : y ∈ B'.U) : B.IsTopBadPoint dim y ↔ B'.IsTopBadPoint dim' y :=
  isTopBadPoint_iff (MPolyfold.topMultiplicity _) hdim hdim' hyU hyU'

open scoped Classical in
/-- **`Θ_k(x)` does not depend on the structure** (the conclusion of 2021 p. 457), for every
ep-groupoid (`dimPart_topDim_eq_of_hasGraphChartAt` without its hypothesis). -/
theorem dimPart_topDim_eq {B B' : X.LocalBranchingStructure Θ x} {dim : B.ι → ℕ}
    {dim' : B'.ι → ℕ} (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i))
    (hdim' : ∀ j, X.PObj.IsSubmanifoldOfDim (B'.M j) (dim' j)) :
    B.dimPart dim (B.topDim dim) x = B'.dimPart dim' (B'.topDim dim') x :=
  dimPart_topDim_eq_of_topMultiplicityAt (fun _ => MPolyfold.topMultiplicityAt x _) hdim hdim'
    B.mem_U B'.mem_U

open scoped Classical in
/-- **2021 Proposition 9.6.5, p. 456 (new in the 2021 edition), slice form, for every
ep-groupoid**: as `proposition_9_6_5`, without the hypothesis `HasGraphChartAt`. -/
theorem proposition_9_6_5_general (B : X.LocalBranchingStructure Θ x) {dim : B.ι → ℕ}
    (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i))
    {i₀ : B.ι} (hi₀ : dim i₀ = B.topDim dim) {W : Set Obj} (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ S : Finset Obj, (∀ y ∈ S, y ∈ W ∧ ∃ i, dim i = B.topDim dim ∧
        X.PObj.submanifoldTangent (B.M i) x = X.PObj.submanifoldTangent (B.M i₀) x ∧
        y ∈ B.M i) ∧
      B.IsTopSlice dim (X.PObj.submanifoldTangent (B.M i₀) x) S := by
  set K := B.topDim dim
  have hA : ∀ i : {i // dim i = K}, X.PObj.IsSubmanifoldOfDim (B.M i.1) K := fun i =>
    (congrArg (X.PObj.IsSubmanifoldOfDim (B.M i.1)) i.2).mp (hdim i.1)
  obtain ⟨F, hFWO, hFL, hF⟩ := MPolyfold.exists_generic_slice_general (fun i : {i // dim i = K} =>
    B.M i.1) hA (fun i => B.mem_M i.1) ⟨i₀, hi₀⟩ B.isOpen_U B.mem_U
    (fun l : {i // dim i < K} => B.M l.1) (fun l => dim l.1)
    (fun l => ⟨hdim l.1, l.2, B.isOpen_diff_M B.isOpen_U subset_rfl l.1⟩) hW hxW
  have : Nonempty Obj := ⟨x⟩
  have hgood : ∀ i : {i // dim i = K},
      X.PObj.submanifoldTangent (B.M i.1) x = X.PObj.submanifoldTangent (B.M i₀) x →
      ∃ y, y ∈ F ∩ B.M i.1 ∧ ∀ y', y' ∈ F ∩ B.M i.1 → y' = y := fun i hi => (hF i).1 hi
  choose! pt hpt hpt_uniq using hgood
  let S : Finset Obj := (Finset.univ.filter fun i : {i // dim i = K} =>
    X.PObj.submanifoldTangent (B.M i.1) x = X.PObj.submanifoldTangent (B.M i₀) x).image pt
  have hSF : ∀ y ∈ S, y ∈ F ∧ ∃ i : {i // dim i = K},
      X.PObj.submanifoldTangent (B.M i.1) x = X.PObj.submanifoldTangent (B.M i₀) x ∧
        y ∈ B.M i.1 := fun y hy => by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hy
    have hi' := (Finset.mem_filter.1 hi).2
    exact ⟨(hpt i hi').1, i, hi', (hpt i hi').2⟩
  refine ⟨S, fun y hy => ?_, fun y hy => ?_, fun i hi => ⟨fun hc => ?_, fun hc y hy => ?_⟩⟩
  · obtain ⟨hyF, i, hi, hyi⟩ := hSF y hy
    exact ⟨(hFWO hyF).1, i.1, i.2, hi, hyi⟩
  · obtain ⟨hyF, -⟩ := hSF y hy
    exact ⟨(hFWO hyF).2, fun i hi => hFL y hyF ⟨i, hi⟩⟩
  · refine ⟨pt ⟨i, hi⟩, ⟨Finset.mem_image_of_mem pt (Finset.mem_filter.2 ⟨Finset.mem_univ _,
      hc⟩), (hpt ⟨i, hi⟩ hc).2⟩, fun y hy => ?_⟩
    exact hpt_uniq ⟨i, hi⟩ hc y ⟨(hSF y hy.1).1, hy.2⟩
  · intro hyi
    have h1 : y ∈ F ∩ B.M (⟨i, hi⟩ : {i // dim i = K}).1 := ⟨(hSF y hy).1, hyi⟩
    rw [(hF ⟨i, hi⟩).2 hc] at h1
    exact h1

open scoped Classical in
/-- **The class weights do not depend on the structure** (2021 p. 457), for every ep-groupoid:
as `sum_class_eq_of_hasGraphChartAt`, without its hypothesis. -/
theorem sum_class_eq
    {B B' : X.LocalBranchingStructure Θ x} {dim : B.ι → ℕ} {dim' : B'.ι → ℕ}
    (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i))
    (hdim' : ∀ j, X.PObj.IsSubmanifoldOfDim (B'.M j) (dim' j)) (T : Set X.PObj.TangentSpace) :
    ∑ i with dim i = B.topDim dim ∧ X.PObj.submanifoldTangent (B.M i) x = T, B.σ i =
      ∑ j with dim' j = B'.topDim dim' ∧ X.PObj.submanifoldTangent (B'.M j) x = T, B'.σ j := by
  have hK : B'.topDim dim' = B.topDim dim := (lemma_9_6_1 hdim hdim').symm
  rw [hK]
  set K := B.topDim dim
  have hO : IsOpen (B.U ∩ B'.U) := B.isOpen_U.inter B'.isOpen_U
  have key := MPolyfold.sum_class_eq hO ⟨B.mem_U, B'.mem_U⟩
    (fun i : {i // dim i = K} => B.M i.1) (fun i => B.σ i.1)
    (fun j : {j // dim' j = K} => B'.M j.1) (fun j => B'.σ j.1)
    (fun l : {l : B.ι ⊕ B'.ι // Sum.elim dim dim' l < K} => Sum.elim B.M B'.M l.1)
    (fun l => Sum.elim dim dim' l.1)
    (fun i => ⟨(congrArg (X.PObj.IsSubmanifoldOfDim (B.M i.1)) i.2).mp (hdim i.1), B.mem_M i.1⟩)
    (fun j => ⟨(congrArg (X.PObj.IsSubmanifoldOfDim (B'.M j.1)) j.2).mp (hdim' j.1),
      B'.mem_M j.1⟩)
    (fun l => by
      obtain ⟨l | l, hl⟩ := l
      · exact ⟨hdim l, hl, B.isOpen_diff_M hO inter_subset_left l⟩
      · exact ⟨hdim' l, hl, B'.isOpen_diff_M hO inter_subset_right l⟩)
    (fun z hzO hzL => by
      have hgen1 : ∀ i, dim i < K → z ∉ B.M i := fun i hi hz => hzL ⟨Sum.inl i, hi⟩ hz
      have hgen2 : ∀ j, dim' j < K → z ∉ B'.M j := fun j hj hz => hzL ⟨Sum.inr j, hj⟩ hz
      rw [sum_subtype_filter (fun i => dim i = K) (fun i => z ∈ B.M i) B.σ,
        sum_subtype_filter (fun j => dim' j = K) (fun j => z ∈ B'.M j) B'.σ]
      have e1 := B.eq_dimPart_topDim hzO.1 hgen1
      have e2 := B'.eq_dimPart_topDim hzO.2 (hK ▸ hgen2)
      rw [hK] at e2
      unfold dimPart at e1 e2
      rw [← e1, ← e2]) T
  simp only [← Finset.sum_filter] at key
  rw [sum_subtype_filter (fun i => dim i = K)
      (fun i => X.PObj.submanifoldTangent (B.M i) x = T) B.σ,
    sum_subtype_filter (fun j => dim' j = K)
      (fun j => X.PObj.submanifoldTangent (B'.M j) x = T) B'.σ] at key
  exact key

/-- **2021 Lemma 9.2.7 (2), p. 412 (2017: Lemma 9.5 (2), p. 300), for every ep-groupoid**: for
an `n`-dimensional local branching structure every `Mᵢ` contains good points converging to `x`
(`lemma_9_2_7_2` with `MPolyfold.hasDomainInvarianceAt`). -/
theorem lemma_9_2_7_2_general (B : X.LocalBranchingStructure Θ x) {n : ℕ} (hdim : B.IsOfDim n)
    (i : B.ι) : ∃ u : ℕ → Obj, (∀ k, u k ∈ B.M i ∧ u k ∈ X.goodSet Θ) ∧
      Tendsto u atTop (𝓝 x) :=
  lemma_9_2_7_2 B hdim (fun y _ => MPolyfold.hasDomainInvarianceAt y n) i

end LocalBranchingStructure

/-! ### Theorem 9.2.1 -/

/-- **2021 Theorem 9.2.1 (1), p. 409 (2017: Theorem 9.1, p. 298), the independence of the tangent
sums, for every ep-groupoid and every `Θ`**: `∑ σᵢ · T_xMᵢ` does not depend on the local
branching structure.  Restrict both structures to labelled ones (Remark 9.1.1,
`MPolyfold.hasLocallyConstantDimAt`), use Proposition 9.1.12 (`dimPartsAgreeNear`) and the
tangent slices (`MPolyfold.hasTangentSlicesAt`). -/
theorem hasIndependentTangentSums (Θ : Obj → ℚ) : X.HasIndependentTangentSums Θ := by
  intro x B B'
  obtain ⟨V, hV, hxV, hVU, dim, hdim⟩ :=
    B.exists_restrict_labelled (MPolyfold.hasLocallyConstantDimAt x)
  obtain ⟨V', hV', hxV', hVU', dim', hdim'⟩ :=
    B'.exists_restrict_labelled (MPolyfold.hasLocallyConstantDimAt x)
  rw [← B.tangentSum_restrict hV hxV hVU, ← B'.tangentSum_restrict hV' hxV' hVU']
  exact (B.restrict hV hxV hVU).tangentSum_eq_of_dimPartsAgreeNear
    (B'.restrict hV' hxV' hVU') hdim hdim'
    (LocalBranchingStructure.dimPartsAgreeNear _ _ hdim hdim')
    fun n => MPolyfold.hasTangentSlicesAt x n

/-! ### Proposition 9.1.11 -/

/-- **A labelled local branching structure exists at every point of `supp(Θ)`**
(`hasLabelledBranchingAt` with `MPolyfold.hasLocallyConstantDimAt`). -/
theorem hasLabelledBranchingAt_general (hΘ : X.IsBranchedEpSubgroupoid Θ) {x : Obj}
    (hx : x ∈ supp Θ) : X.HasLabelledBranchingAt Θ x :=
  hasLabelledBranchingAt hΘ (MPolyfold.hasLocallyConstantDimAt x) hx

/-- **`(Θ_k)` is a dimensional decomposition of `Θ`** (2021 Proposition 9.1.11 (1), (2), p. 407),
for every branched ep⁺-subgroupoid of every ep-groupoid. -/
theorem isDimDecomposition_dimComponent_general (hΘ : X.IsBranchedEpSubgroupoid Θ) :
    X.IsDimDecomposition Θ (X.dimComponent Θ) :=
  isDimDecomposition_dimComponent proposition_9_1_12 hΘ fun x _ =>
    MPolyfold.hasLocallyConstantDimAt x

/-- **`(Θ_k)` is a local dimensional decomposition**, for every branched ep⁺-subgroupoid. -/
theorem isLocalDimDecomposition_dimComponent_general (hΘ : X.IsBranchedEpSubgroupoid Θ) :
    X.IsLocalDimDecomposition Θ (X.dimComponent Θ) :=
  isLocalDimDecomposition_dimComponent proposition_9_1_12 hΘ fun x _ =>
    MPolyfold.hasLocallyConstantDimAt x

/-- **2021 Proposition 9.1.11, p. 407, existence and uniqueness** (in the reading of its proof),
for every branched ep⁺-subgroupoid of every ep-groupoid: there is exactly one local
dimensional decomposition. -/
theorem existsUnique_localDimDecomposition_general (hΘ : X.IsBranchedEpSubgroupoid Θ) :
    ∃! Θk, X.IsDimDecomposition Θ Θk ∧ X.IsLocalDimDecomposition Θ Θk :=
  existsUnique_localDimDecomposition proposition_9_1_12 hΘ fun x _ =>
    MPolyfold.hasLocallyConstantDimAt x

/-- **2021 Proposition 9.1.11, uniqueness, for every ep-groupoid**: two local dimensional
decompositions of a branched ep⁺-subgroupoid are equal (replacing
`proposition_9_1_11_unique_of_hasGraphChartAt`). -/
theorem proposition_9_1_11_unique (hΘ : X.IsBranchedEpSubgroupoid Θ) {Θk Θk' : ℕ → Obj → ℚ}
    (h : X.IsDimDecomposition Θ Θk) (h' : X.IsDimDecomposition Θ Θk')
    (hl : X.IsLocalDimDecomposition Θ Θk) (hl' : X.IsLocalDimDecomposition Θ Θk') : Θk = Θk' :=
  isDimDecomposition_unique proposition_9_1_12 hΘ h h' hl hl'

/-- **Local finiteness of `(Θ_k)` at the points of `supp(Θ)`, for every ep-groupoid**: no bound
on the dimensions is needed there. -/
theorem dimComponent_locallyFinite_of_mem_general (hΘ : X.IsBranchedEpSubgroupoid Θ) {y : Obj}
    (hy : y ∈ supp Θ) : ∃ W ∈ 𝓝 y, {k | ∃ z ∈ W, X.dimComponent Θ k z ≠ 0}.Finite :=
  dimComponent_locallyFinite_of_mem proposition_9_1_12 hΘ
    (fun x _ => MPolyfold.hasLocallyConstantDimAt x) hy

/-- **2021 Proposition 9.1.11, p. 407, in the reading of its proof**, for every ep-groupoid
whose submanifolds have dimensions bounded by some `N` (the bound is used only for the local
finiteness off `supp(Θ)`); Proposition 9.1.12 and Remark 9.1.1 are no longer hypotheses
(`proposition_9_1_11_local_of`).  The bound can be met: `rn_hasDimAt_le`. -/
theorem proposition_9_1_11_local_of_le {N : ℕ}
    (hN : ∀ (A : Set Obj) (a : Obj) (n : ℕ), X.PObj.IsSmoothSubmanifold A →
      X.PObj.HasDimAt A a n → n ≤ N) :
    X.Proposition_9_1_11_local :=
  proposition_9_1_11_local_of proposition_9_1_12 (fun x => MPolyfold.hasLocallyConstantDimAt x)
    hN

/-! ### Lemma 9.3.4 -/

/-- **2021 Lemma 9.3.4, p. 423 (2017: Lemma 9.10), from the ball form of the graph
representation alone**: as `lemma_9_3_4_of_hasGraphBallAt`, without the hypothesis
`HasContinuousLevelOneOn` (it holds for every smooth finite-dimensional submanifold,
`MPolyfold.hasContinuousLevelOneOn`). -/
theorem lemma_9_3_4_of_hasGraphBallAt' (hΘ : X.IsBranchedEpSubgroupoid Θ) {n : ℕ}
    {T₁ T₂ : Obj → X.PObj.OrTangent →₀ ℚ} (h₁ : X.IsOrientationOfDim Θ n T₁)
    (h₂ : X.IsOrientationOfDim Θ n T₂) (hG : ∀ x ∈ supp Θ, X.PObj.HasGraphBallAt x n)
    (hagree : ∀ y ∈ X.goodSet Θ, T₁ y = T₂ y) :
    ∀ x ∈ X.PObj.smoothSet, T₁ x = T₂ x :=
  lemma_9_3_4_of_hasGraphBallAt hΘ h₁ h₂ hG (fun _ hA => MPolyfold.hasContinuousLevelOneOn hA)
    hagree

/-- **2021 Lemma 9.3.4, p. 423 (2017: Lemma 9.10), on the interior `X ∖ ∂X`**: for a branched
ep⁺-subgroupoid whose support consists of points of degeneracy index `0` (Definition 2.22; e.g.
every `Θ` on an M-polyfold without boundary), two `n`-dimensional orientations which agree at
the good points agree on `X_∞`.  The hypothesis can be met: `MPolyfold.degIndex_rn`. -/
theorem lemma_9_3_4_of_degIndex_eq_zero (hΘ : X.IsBranchedEpSubgroupoid Θ) {n : ℕ}
    {T₁ T₂ : Obj → X.PObj.OrTangent →₀ ℚ} (h₁ : X.IsOrientationOfDim Θ n T₁)
    (h₂ : X.IsOrientationOfDim Θ n T₂) (hint : ∀ x ∈ supp Θ, X.PObj.degIndex x = 0)
    (hagree : ∀ y ∈ X.goodSet Θ, T₁ y = T₂ y) :
    ∀ x ∈ X.PObj.smoothSet, T₁ x = T₂ x :=
  lemma_9_3_4_of_hasGraphBallAt' hΘ h₁ h₂ (fun x hx => by
    obtain ⟨φ, hφ, hxφ, hi⟩ := MPolyfold.exists_chart_mem_interior_of_degIndex_eq_zero (hint x hx)
    exact MPolyfold.hasGraphBallAt_of_mem_interior hφ hxφ hi n) hagree


end EpGroupoid

end Polyfold
