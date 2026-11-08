import Polyfold.Chapter9.Appendix
import Polyfold.Chapter9.TangentSlices

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.6.1: **Proposition 9.6.5** (p. 456) and the formula on p. 457 (new in the
2021 edition), and from them **Proposition 9.1.12** (p. 408; new in the 2021 edition) and
the independence part of **Theorem 9.2.1** (pp. 409–410; 2017: Theorem 9.1, p. 298) for
branched ep⁺-subgroupoids that need not be equidimensional; and part of the hypotheses of
**Definition 9.2.12** (p. 418; 2017: Definition 9.6, p. 306).  `Appendix.lean` proves
Proposition 9.1.12 under the hypothesis `MPolyfold.TopMultiplicity`; here that hypothesis is
derived from the graph representation of Lemmas 9.2.9–9.2.11 (`TangentSlicesBasic.lean`).

# Top slices: Proposition 9.6.5 and the formula of p. 457

## The text, paraphrased

(pp. 456–457) At a top-bad point `x`, the top indices `I_k` are grouped into classes `Ξ` by
`T_xMᵢ = T_xMᵢ'`, an argument "similar to Proposition 9.2.8".  (Proposition 9.6.5) Each class
splits into nonempty disjoint `I¹, …, I^p`, with sequences of top-good points `x^e_j → x` lying
on `Mᵢ` exactly for `i ∈ I^e`.  Then `Θ_k(x) = ∑_Ξ ∑_e Θ_k(x^e)`, and the right side is said
not to depend on the structure.

## What is formalized

* `MPolyfold.HasGraphChartAt x`: one chart at `x` and one set of admissible directions in which
  every smooth finite-dimensional submanifold through `x`, of any dimension, has the graph
  representation (`IsGraphChartAt`).  As in the proofs of Lemmas 9.2.9–9.2.11 the text works in
  one chart at `x`.  It implies `HasGraphChartsAt x n` for every `n`.  Witness:
  `hasGraphChartAt_rn` (every point of `ℝᵐ`).
* **Generic tangent slices** (`exists_slice_of_isGraphChartAt`, `exists_generic_slice`): for
  `k`-dimensional sheets through `x` and finitely many submanifolds `L_l` of smaller dimension,
  each open set `W ∋ x` contains a slice `F` that meets each sheet tangent to a given one in
  exactly one point, misses the other sheets, and misses every `L_l`.
* **`TopMultiplicity` from the graph representation**: `topMultiplicityAt_of_hasGraphChartAt`,
  `topMultiplicity_of_hasGraphChartAt`; in `ℝᵐ` for all `m` and all `k`: `topMultiplicity_rn`.
* **Proposition 9.6.5** (slice form) `LocalBranchingStructure.proposition_9_6_5`, with
  `IsTopSlice`; **the formula of p. 457** `dimPart_topDim_eq_sum_slices` (one class:
  `sum_class_eq_sum_of_isTopSlice`); **its independence of the structure**
  `sum_class_eq_of_hasGraphChartAt`, `dimPart_topDim_eq_of_hasGraphChartAt`.
* **Proposition 9.1.12**: `dimPartsAgreeNear_of_hasGraphChartAt` (graph representation on
  `supp(Θ)` only), `EpGroupoid.proposition_9_1_12_of_hasGraphChartAt`; in `ℝᵐ` with no
  hypothesis: `proposition_9_1_12_rn`, `proposition_9_1_12_trivial_rn`.  **Lemma 9.6.4**:
  `lemma_9_6_4_of_hasGraphChartAt`.
* **Remark 9.1.1** (p. 402; 2017: Remark 9.1, p. 291), local constancy of the dimension:
  `MPolyfold.HasLocallyConstantDimAt`, proved in `ℝᵐ` (`hasLocallyConstantDimAt_rn`: `T_yA` is
  the range of the projection `Ds(y)`, so its dimension is `trace Ds(y)`, continuous in `y`).
* **Theorem 9.2.1, independence**: `hasIndependentTangentSums_of_hasGraphChartAt` (labelled
  structures), `hasIndependentTangentSums_of_hasGraphChartAt_of_hasLocallyConstantDimAt` (no
  labels); in `ℝᵐ` for every `Θ`, with no hypothesis: `hasIndependentTangentSums_rn`.
* **Definition 9.2.12**: `TMᵢ` is a sub-M-polyfold of `TX` (Definition 2.20), with retraction
  `Ts` (`IsSmoothSubmanifold.isSubMPolyfold_tangent`,
  `LocalBranchingStructure.isSubMPolyfold_tangentSubmanifold`); in `ℝᵐ` the conclusion of
  Definition 9.2.12 needs no independence hypothesis (`isBranchedEpSubgroupoid_tangentTheta_rn`).
* Witnesses: `Remark913Hyp.exists_mixed_rn_two` (in `ℝ²`, two labelled structures of one
  branched `Θ` with sheets of dimensions `1` and `0`, different sheets, the dimensional parts
  and the tangent sums agree); `rnPolyfold_isSubMPolyfold_tangent_graph2` (the tangent of the
  line `{r₁ = 0}` is a sub-M-polyfold of `T(ℝ²)`, nonempty and not all of `T(ℝ²)`).

## The two steps `Appendix.lean` left open, and how they are supplied

* Lemma 9.6.4, "as in the discussion of good points": what is needed is `Θ'_k(y) = σ`, i.e.
  `TopMultiplicityAt y`.  Proof: the sheets through `y` of both structures are grouped by
  tangent space; per class, a generic slice (direction `h₀` in the class tangent space, off all
  other tangent spaces and off the `T_yL_l` of the lower-dimensional sets through `y`; the
  others are avoided by shrinking `W`) meets each sheet of the class once, so the class weight
  is `∑_{z ∈ F} Θ(z)` for both families.  The lower-dimensional `L_l` through `y` are avoided by
  the uniform approximation `IsGraphChartAt.approx` of `L_l` in the same chart; this is why a
  common chart for all dimensions (`HasGraphChartAt`) is used.
* p. 457, independence of the right side: one slice is chosen for the sheets of *both*
  structures at once.  Its points lie off the lower-dimensional sets of both, so there
  `Θ_k = Θ = Θ'_k`, and the class weights of the two structures are the same sum of values of
  `Θ` (`sum_class_eq_of_hasGraphChartAt`).

## What the text leaves implicit, and the choices made

* The points `x^e` of Proposition 9.6.5 are replaced by the points of a slice `S` in an
  arbitrary neighbourhood `W` of `x` (instead of sequences); `I^e` is the set of indices of the
  sheets through the `e`-th point, and the `I^e` partition the class since each sheet of the
  class meets `S` once.  The points are not asserted to be top-good; the formula needs only
  that they lie off the lower-dimensional sheets and off the other top classes.  Proposition
  9.6.5 is proved at every `x`, top-bad or not, and without the branched hypothesis on `Θ`.
* `HasGraphChartsAt` (one chart per dimension) is not enough for this argument: avoiding the
  `L_l` would need the approximation of `L_l` read in the chart of the top dimension, a chart
  change at level `0` that is not formalized.

## Not formalized, and why

* Top-goodness of the points `x^e`, and the sequences (see above).
* That `Ts` is an sc⁺-retraction of `TX` (`Ts(TV) ⊆ (TX)_1`, `1 ∘ Ts` sc-smooth into `(TX)¹`), so
  `TMᵢ` is a smooth finite-dimensional submanifold of `TX`: the remaining field
  `TangentBranchingHyp.isSmoothSubmanifold`.  It needs that the tangent map of an sc⁺-map
  raises levels in the tangent M-polyfold, which Part I does not formalize.
* The graph representation in general M-polyfolds (sc-calculus at level `0`, as in
  `TangentSlicesBasic.lean`).
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Module

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

variable (P) in
/-- **The graph representation at `x` in one chart for all dimensions** (the content of 2021
Lemmas 9.2.9–9.2.11, pp. 414–417, used in 2021 Proposition 9.6.5, p. 456; the text works in one
chart at `x`): one chart `φ` at `x` and one set `K` of admissible directions in which every
smooth finite-dimensional submanifold through `x`, of any dimension, has the graph
representation `IsGraphChartAt`.  Satisfiable: `hasGraphChartAt_rn`. -/
def HasGraphChartAt (x : X) : Prop :=
  ∃ (φ : MChart X) (hφ : P.IsChart φ), x ∈ φ.source ∧ ∃ K : Set (φ.model.E 0),
    ∀ (A : Set X) (n : ℕ), P.IsSubmanifoldOfDim A n → x ∈ A → P.IsGraphChartAt hφ K A x

/-- One chart for all dimensions gives one chart per dimension. -/
theorem HasGraphChartAt.hasGraphChartsAt {x : X} (h : P.HasGraphChartAt x) (n : ℕ) :
    P.HasGraphChartsAt x n := by
  obtain ⟨φ, hφ, hxφ, K, hK⟩ := h
  exact ⟨φ, hφ, hxφ, K, fun A hA hx => hK A n hA hx⟩

/-- **The graph representation in `ℝᵐ`** (from `isGraphChartAt_rn`, in the chart `id`). -/
theorem hasGraphChartAt_rn {m : ℕ} (x : Fin m → ℝ) : (rnPolyfold m).HasGraphChartAt x :=
  ⟨rnChart m 0, isChart_rnChart 0, mem_univ x, univ, fun _ _ hA hx => isGraphChartAt_rn hA.1 hx⟩

/-- **Tangent slices for a finite family of sheets** (the slice form of 2021 Proposition 9.2.8,
p. 413, as in `hasTangentSlicesAt_of_hasGraphChartsAt`), with a family of any dimensions in
place of an equidimensional one: if no tangent space different from `T_xA_{k₀}` contains it,
every open `W ∋ x` contains a set meeting each sheet tangent to `A_{k₀}` in exactly one point
and missing the others. -/
theorem exists_slice_of_isGraphChartAt {x : X} {φ : MChart X} (hφ : P.IsChart φ)
    (hxφ : x ∈ φ.source) {K : Set (φ.model.E 0)} {κ : Type*} [Finite κ] (A : κ → Set X)
    (hA : ∀ k, P.IsSmoothSubmanifold (A k)) (hx : ∀ k, x ∈ A k)
    (hg : ∀ k, P.IsGraphChartAt hφ K (A k) x) (k₀ : κ)
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
  have hh₀K : h₀ ∈ K := hK h₀ hh₀T hh₀r
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
    (hg k).graph Q (hQT k hk) (hQid k hk) h₀ (by rw [hT k hk]; exact hh₀T) hh₀K (ε / 2)
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

/-- Tangent spaces of a smaller or equal dimension do not contain a different one. -/
theorem not_chartTangent_subset {φ : MChart X} (hφ : P.IsChart φ) {x : X} (hxφ : x ∈ φ.source)
    {A B : Set X} {a b : ℕ} (hA : P.IsSmoothSubmanifold A) (hAx : P.HasDimAt A x a)
    (hB : P.IsSmoothSubmanifold B) (hBx : P.HasDimAt B x b) (hba : b ≤ a)
    (hne : P.chartTangent hφ B x ≠ P.chartTangent hφ A x) :
    ¬ P.chartTangent hφ A x ⊆ P.chartTangent hφ B x := by
  intro hsub
  obtain ⟨NA, hNA, hfinA⟩ := exists_submodule_chartTangent hφ hA hAx.1 hxφ
  obtain ⟨NB, hNB, hfinB⟩ := exists_submodule_chartTangent hφ hB hBx.1 hxφ
  have hra := finrank_chartTangent hφ hAx hA hxφ hNA
  have hrb := finrank_chartTangent hφ hBx hB hxφ hNB
  have hle : NA ≤ NB := by
    rw [← SetLike.coe_subset_coe, hNA, hNB]; exact hsub
  have := Submodule.finrank_mono hle
  have hEq : NA = NB := Submodule.eq_of_le_of_finrank_eq hle (by omega)
  exact hne (by rw [← hNA, ← hNB, hEq])

/-- Equal chart tangent spaces have equal dimensions. -/
theorem HasDimAt.eq_of_chartTangent_eq {φ : MChart X} (hφ : P.IsChart φ) {x : X}
    (hxφ : x ∈ φ.source) {A B : Set X} {a b : ℕ} (hA : P.IsSmoothSubmanifold A)
    (hAx : P.HasDimAt A x a) (hB : P.IsSmoothSubmanifold B) (hBx : P.HasDimAt B x b)
    (h : P.chartTangent hφ A x = P.chartTangent hφ B x) : a = b := by
  obtain ⟨NA, hNA, hfinA⟩ := exists_submodule_chartTangent hφ hA hAx.1 hxφ
  obtain ⟨NB, hNB, hfinB⟩ := exists_submodule_chartTangent hφ hB hBx.1 hxφ
  have hEq : NA = NB := by rw [← SetLike.coe_set_eq, hNA, hNB, h]
  rw [← finrank_chartTangent hφ hAx hA hxφ hNA, ← finrank_chartTangent hφ hBx hB hxφ hNB, hEq]

/-- **Generic tangent slices** (for 2021 Proposition 9.6.5, p. 456): for `k`-dimensional sheets
through `x` and finitely many submanifolds `L_l` of dimension `< k`, each closed in an open
`O ∋ x`, every open `W ∋ x` contains a slice for the class of `A_{j₀}` that misses every `L_l`.
The `L_l` through `x` are added to the family (their tangent spaces do not contain `T_xA_{j₀}`),
the others are avoided by shrinking `W` to `W ∩ (O ∖ L_l)`. -/
theorem exists_generic_slice {x : X} (hG : P.HasGraphChartAt x) {k : ℕ} {κ ν : Type*}
    [Finite κ] [Finite ν] (A : κ → Set X) (hA : ∀ j, P.IsSubmanifoldOfDim (A j) k)
    (hx : ∀ j, x ∈ A j) (j₀ : κ) {O : Set X} (hO : IsOpen O) (hxO : x ∈ O)
    (L : ν → Set X) (dL : ν → ℕ)
    (hL : ∀ l, P.IsSubmanifoldOfDim (L l) (dL l) ∧ dL l < k ∧ IsOpen (O \ L l))
    {W : Set X} (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ F ⊆ W ∩ O, (∀ y ∈ F, ∀ l, y ∉ L l) ∧ ∀ j,
      (P.submanifoldTangent (A j) x = P.submanifoldTangent (A j₀) x → ∃! y, y ∈ F ∩ A j) ∧
      (P.submanifoldTangent (A j) x ≠ P.submanifoldTangent (A j₀) x → F ∩ A j = ∅) := by
  classical
  obtain ⟨φ, hφ, hxφ, K, hGA⟩ := hG
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
  have hg : ∀ k', P.IsGraphChartAt hφ K (A' k') x := fun k' => by
    obtain ⟨d, -, hd⟩ := hdim k'
    exact hGA _ d hd (hA'x k')
  have hnle : ∀ k', P.chartTangent hφ (A' k') x ≠ P.chartTangent hφ (A' (Sum.inl j₀)) x →
      ¬ P.chartTangent hφ (A' (Sum.inl j₀)) x ⊆ P.chartTangent hφ (A' k') x := fun k' hne => by
    obtain ⟨d, hdk, hd⟩ := hdim k'
    exact not_chartTangent_subset hφ hxφ (hA j₀).1 ((hA j₀).2 x (hx j₀)) hd.1
      (hd.2 x (hA'x k')) hdk hne
  obtain ⟨F, hFW, hF⟩ := exists_slice_of_isGraphChartAt hφ hxφ A' (fun k' => by
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
variable (P) in
/-- `MPolyfold.TopMultiplicity` (`Appendix.lean`) at one point `x`: the condition needed in the
proofs of 2021 Lemma 9.6.4 (p. 455) and of the independence on p. 457. -/
def TopMultiplicityAt (x : X) (k : ℕ) : Prop :=
  ∀ (O : Set X), IsOpen O → x ∈ O →
    ∀ (ι κ ν : Type u) [Fintype ι] [Fintype κ] [Fintype ν] (M : ι → Set X) (σ : ι → ℚ)
      (N : κ → Set X) (τ : κ → ℚ) (L : ν → Set X) (dL : ν → ℕ),
      (∀ i, P.IsSubmanifoldOfDim (M i) k ∧ x ∈ M i ∧ IsOpen (O \ M i) ∧ 0 < σ i) →
      (∀ j, P.IsSubmanifoldOfDim (N j) k ∧ x ∈ N j ∧ IsOpen (O \ N j) ∧ 0 < τ j) →
      (∀ l, P.IsSubmanifoldOfDim (L l) (dL l) ∧ dL l < k ∧ IsOpen (O \ L l)) →
      (∀ y ∈ O, (∀ l, y ∉ L l) → ∑ i with y ∈ M i, σ i = ∑ j with y ∈ N j, τ j) →
      ∑ i, σ i = ∑ j, τ j

/-- `TopMultiplicity` is `TopMultiplicityAt` at every point. -/
theorem topMultiplicity_iff {k : ℕ} : P.TopMultiplicity k ↔ ∀ x, P.TopMultiplicityAt x k :=
  Iff.rfl

open scoped Classical in
/-- A sum split over the classes of `f` (the classes `Ξ` of p. 457). -/
theorem sum_eq_sum_classes {ι β : Type*} [Fintype ι] (f : ι → β) (σ : ι → ℚ) (Ts : Finset β)
    (hTs : ∀ i, f i ∈ Ts) : ∑ i, σ i = ∑ T ∈ Ts, ∑ i, if f i = T then σ i else 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_ite_eq, if_pos (hTs i)]

open scoped Classical in
/-- **The class weights of two families agree** (2021 p. 457, for two weighted families of
`k`-dimensional sheets with the same counting function off the lower-dimensional `L_l`): one
generic slice serves both families, so each class weight is the sum of the counting function
over the slice. -/
theorem sum_class_eq_of_hasGraphChartAt {x : X} (hG : P.HasGraphChartAt x) {k : ℕ} {O : Set X}
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
  obtain ⟨F, hFWO, hFL, hF⟩ := exists_generic_slice hG A hAd hAx k₀ hO hxO L dL hL hO hxO
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
/-- **`TopMultiplicity` from the graph representation** (supplying the step of 2021 Lemma 9.6.4,
p. 455, "as in the discussion of good points"): summing the class weights. -/
theorem topMultiplicityAt_of_hasGraphChartAt {x : X} (hG : P.HasGraphChartAt x) (k : ℕ) :
    P.TopMultiplicityAt x k := by
  intro O hO hxO ι κ ν _ _ _ M σ N τ L dL hM hN hL hagree
  have hclass := sum_class_eq_of_hasGraphChartAt hG hO hxO M σ N τ L dL
    (fun i => ⟨(hM i).1, (hM i).2.1⟩) (fun j => ⟨(hN j).1, (hN j).2.1⟩) hL hagree
  set Ts : Finset (Set P.TangentSpace) :=
    Finset.univ.image (fun i => P.submanifoldTangent (M i) x) ∪
      Finset.univ.image (fun j => P.submanifoldTangent (N j) x)
  rw [sum_eq_sum_classes (fun i => P.submanifoldTangent (M i) x) σ Ts
      (fun i => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))),
    sum_eq_sum_classes (fun j => P.submanifoldTangent (N j) x) τ Ts
      (fun j => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))]
  exact Finset.sum_congr rfl fun T _ => hclass T

/-- **`MPolyfold.TopMultiplicity`** (the hypothesis of `proposition_9_1_12_of_topMultiplicity`)
under the graph representation at every point. -/
theorem topMultiplicity_of_hasGraphChartAt (hG : ∀ x, P.HasGraphChartAt x) (k : ℕ) :
    P.TopMultiplicity k := fun x => topMultiplicityAt_of_hasGraphChartAt (hG x) k

/-- **`TopMultiplicity` in `ℝᵐ`** for every `m` and every `k` (`Appendix.lean` has `k = 0` and
`k ≥ m`). -/
theorem topMultiplicity_rn (m k : ℕ) : (rnPolyfold m).TopMultiplicity k :=
  topMultiplicity_of_hasGraphChartAt hasGraphChartAt_rn k

end MPolyfold

/-! ### Proposition 9.1.12 and Lemma 9.6.4 -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ}

namespace LocalBranchingStructure

variable {x : Obj} {B B' : X.LocalBranchingStructure Θ x} {dim : B.ι → ℕ} {dim' : B'.ι → ℕ}

open scoped Classical in
/-- The top parts agree at `y`, under `TopMultiplicityAt y` if `y ∈ supp(Θ)` (as
`dimPart_topDim_eq_of_topMultiplicity` of `Appendix.lean`, with the hypothesis at `y` only). -/
theorem dimPart_topDim_eq_of_topMultiplicityAt {y : Obj}
    (hT : y ∈ supp Θ → X.PObj.TopMultiplicityAt y (B.topDim dim))
    (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i))
    (hdim' : ∀ j, X.PObj.IsSubmanifoldOfDim (B'.M j) (dim' j)) (hyU : y ∈ B.U)
    (hyU' : y ∈ B'.U) :
    B.dimPart dim (B.topDim dim) y = B'.dimPart dim' (B'.topDim dim') y := by
  by_cases hy : y ∉ supp Θ
  · have h1 : y ∉ B.topUnion dim (B.topDim dim) := fun h => by
      obtain ⟨i, -, hyi⟩ := B.mem_topUnion.1 h
      exact hy ((B.mem_supp_iff hyU).2 ⟨i, hyi⟩)
    have h2 : y ∉ B'.topUnion dim' (B'.topDim dim') := fun h => by
      obtain ⟨j, -, hyj⟩ := B'.mem_topUnion.1 h
      exact hy ((B'.mem_supp_iff hyU').2 ⟨j, hyj⟩)
    rw [B.dimPart_eq_zero_of_notMem_topUnion h1, B'.dimPart_eq_zero_of_notMem_topUnion h2]
  push Not at hy
  have hK : B'.topDim dim' = B.topDim dim := (lemma_9_6_1 hdim hdim').symm
  rw [hK]
  set K := B.topDim dim
  set O := (B.U ∩ B'.U) ∩ (B.nbhdAt y ∩ B'.nbhdAt y)
  have hO : IsOpen O := (B.isOpen_U.inter B'.isOpen_U).inter
    ((B.isOpen_nbhdAt y).inter (B'.isOpen_nbhdAt y))
  have hyO : y ∈ O := ⟨⟨hyU, hyU'⟩, B.mem_nbhdAt_self hyU, B'.mem_nbhdAt_self hyU'⟩
  have key := hT hy O hO hyO {i // dim i = K ∧ y ∈ B.M i} {j // dim' j = K ∧ y ∈ B'.M j}
    {l : B.ι ⊕ B'.ι // Sum.elim dim dim' l < K} (fun i => B.M i.1) (fun i => B.σ i.1)
    (fun j => B'.M j.1) (fun j => B'.σ j.1) (fun l => Sum.elim B.M B'.M l.1)
    (fun l => Sum.elim dim dim' l.1)
    (fun i => ⟨(congrArg _ i.2.1).mp (hdim i.1), i.2.2, B.isOpen_diff_M hO (fun z hz => hz.1.1) i.1,
      B.σ_pos i.1⟩)
    (fun j => ⟨(congrArg _ j.2.1).mp (hdim' j.1), j.2.2,
      B'.isOpen_diff_M hO (fun z hz => hz.1.2) j.1, B'.σ_pos j.1⟩)
    (fun l => by
      obtain ⟨l | l, hl⟩ := l
      · exact ⟨hdim l, hl, B.isOpen_diff_M hO (fun z hz => hz.1.1) l⟩
      · exact ⟨hdim' l, hl, B'.isOpen_diff_M hO (fun z hz => hz.1.2) l⟩)
    (fun z hzO hzL => by
      have hgen1 : ∀ i, dim i < K → z ∉ B.M i := fun i hi hz => hzL ⟨Sum.inl i, hi⟩ hz
      have hgen2 : ∀ j, dim' j < K → z ∉ B'.M j := fun j hj hz => hzL ⟨Sum.inr j, hj⟩ hz
      refine (sum_subtype_filter (fun i => dim i = K ∧ y ∈ B.M i) (fun i => z ∈ B.M i)
        B.σ).trans (Eq.trans ?_ (sum_subtype_filter (fun j => dim' j = K ∧ y ∈ B'.M j)
        (fun j => z ∈ B'.M j) B'.σ).symm)
      have e1 : ∑ i with (dim i = K ∧ y ∈ B.M i) ∧ z ∈ B.M i, B.σ i = Θ z := by
        rw [B.eq_dimPart_topDim hzO.1.1 hgen1]
        unfold dimPart
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hzO.2.1.2 i h.2⟩, h.2⟩⟩
      have e2 : ∑ j with (dim' j = K ∧ y ∈ B'.M j) ∧ z ∈ B'.M j, B'.σ j = Θ z := by
        rw [B'.eq_dimPart_topDim hzO.1.2 (hK ▸ hgen2), hK]
        unfold dimPart
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hzO.2.2.2 j h.2⟩, h.2⟩⟩
      rw [e1, e2])
  unfold dimPart
  rw [Finset.sum_subtype (Finset.univ.filter fun i => dim i = K ∧ y ∈ B.M i)
      (p := fun i => dim i = K ∧ y ∈ B.M i) (by simp),
    Finset.sum_subtype (Finset.univ.filter fun j => dim' j = K ∧ y ∈ B'.M j)
      (p := fun j => dim' j = K ∧ y ∈ B'.M j) (by simp)]
  exact key

open scoped Classical in
/-- The descending induction of 2021 p. 454 with `TopMultiplicityAt` on `supp(Θ)` only. -/
theorem dimPartsAgreeNear_of_topMultiplicityAt_aux (n : ℕ) :
    ∀ (Θ : Obj → ℚ), (∀ y ∈ supp Θ, ∀ k, X.PObj.TopMultiplicityAt y k) →
      ∀ (B B' : X.LocalBranchingStructure Θ x) (dim : B.ι → ℕ) (dim' : B'.ι → ℕ),
      (∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i)) →
      (∀ j, X.PObj.IsSubmanifoldOfDim (B'.M j) (dim' j)) →
      Fintype.card B.ι + Fintype.card B'.ι = n → DimPartsAgreeNear B B' dim dim' := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Θ hT B B' dim dim' hdim hdim' hn
  have hO : IsOpen (B.U ∩ B'.U) := B.isOpen_U.inter B'.isOpen_U
  have hxO : x ∈ B.U ∩ B'.U := ⟨B.mem_U, B'.mem_U⟩
  have hΘx : ∀ (C : X.LocalBranchingStructure Θ x), IsEmpty C.ι → Θ x = 0 := fun C hC => by
    rw [C.eq_sum x C.mem_U]
    exact Finset.sum_eq_zero fun i _ => hC.elim i
  have hΘx' : ∀ (C : X.LocalBranchingStructure Θ x), Nonempty C.ι → 0 < Θ x := fun C hC => by
    obtain ⟨i⟩ := hC
    exact (C.mem_supp_iff C.mem_U).2 ⟨i, C.mem_M i⟩
  rcases isEmpty_or_nonempty B.ι with hB | hB <;> rcases isEmpty_or_nonempty B'.ι with hB' | hB'
  · refine ⟨B.U ∩ B'.U, hO, hxO, subset_rfl, fun k y _ => ?_⟩
    unfold dimPart
    rw [Finset.sum_eq_zero fun i _ => hB.elim i, Finset.sum_eq_zero fun j _ => hB'.elim j]
  · exact absurd (hΘx' B' hB') (by rw [hΘx B hB]; exact lt_irrefl 0)
  · exact absurd (hΘx' B hB) (by rw [hΘx B' hB']; exact lt_irrefl 0)
  · have hK : B'.topDim dim' = B.topDim dim := (lemma_9_6_1 hdim hdim').symm
    set K := B.topDim dim with hKdef
    have htop : ∀ y ∈ B.U ∩ B'.U, B.dimPart dim K y = B'.dimPart dim' K y := fun y hy => by
      have := dimPart_topDim_eq_of_topMultiplicityAt (fun hy' => hT y hy' K) hdim hdim'
        hy.1 hy.2
      rwa [hK] at this
    set Θ' : Obj → ℚ := fun y => ∑ i with dim i ≠ K ∧ y ∈ B.M i, B.σ i with hΘ'
    have hBL : ∀ y ∈ B.U ∩ B'.U, Θ' y = ∑ i with dim i ≠ K ∧ y ∈ B.M i, B.σ i :=
      fun y _ => rfl
    have hB'L : ∀ y ∈ B.U ∩ B'.U, Θ' y = ∑ j with dim' j ≠ K ∧ y ∈ B'.M j, B'.σ j := by
      intro y hy
      have h1 := B.eq_dimPart_add (dim := dim) K hy.1
      have h2 := B'.eq_dimPart_add (dim := dim') K hy.2
      rw [htop y hy] at h1
      change ∑ i with dim i ≠ K ∧ y ∈ B.M i, B.σ i = _
      linarith
    have hsupp : ∀ y ∈ supp Θ', y ∈ supp Θ := fun y hy => by
      by_contra hy'
      have h0 : Θ' y = 0 := Finset.sum_eq_zero fun i hi => by
        have hyi := (Finset.mem_filter.1 hi).2.2
        exact absurd ((B.mem_supp_iff (B.subset_U i hyi)).2 ⟨i, hyi⟩) hy'
      have h1 : (0 : ℚ) < Θ' y := hy
      rw [h0] at h1
      exact lt_irrefl 0 h1
    set BL := B.subOn (fun i => dim i ≠ K) hO hxO inter_subset_left Θ' hBL
    set B'L := B'.subOn (fun j => dim' j ≠ K) hO hxO inter_subset_right Θ' hB'L
    obtain ⟨i₀, hi₀⟩ := B.exists_dim_eq_topDim dim
    have hcard : Fintype.card BL.ι + Fintype.card B'L.ι < n := by
      have h1 : Fintype.card {i // dim i ≠ K} < Fintype.card B.ι :=
        Fintype.card_subtype_lt (x := i₀) (by simp [hi₀, hKdef])
      have h2 : Fintype.card {j // dim' j ≠ K} ≤ Fintype.card B'.ι :=
        Fintype.card_subtype_le _
      have h1' : Fintype.card BL.ι < Fintype.card B.ι := h1
      have h2' : Fintype.card B'L.ι ≤ Fintype.card B'.ι := h2
      omega
    obtain ⟨V, hV, hxV, hVU, hVk⟩ := ih _ hcard Θ' (fun y hy k => hT y (hsupp y hy) k) BL B'L
      (fun i => dim i.1) (fun j => dim' j.1)
      (fun i => (hdim i.1).inter_isOpen hO) (fun j => (hdim' j.1).inter_isOpen hO) rfl
    have hVO : V ⊆ B.U ∩ B'.U := fun y hy => (hVU hy).1
    refine ⟨V, hV, hxV, hVO, fun k y hy => ?_⟩
    by_cases hk : k = K
    · subst hk; exact htop y (hVO hy)
    · have := hVk k y hy
      rw [subOn_dimPart B _ hO hxO inter_subset_left Θ' hBL dim k (hVO hy),
        subOn_dimPart B' _ hO hxO inter_subset_right Θ' hB'L dim' k (hVO hy)] at this
      rw [B.dimPart_eq_sum_ne dim hk, B'.dimPart_eq_sum_ne dim' hk]
      exact this

/-- **2021 Proposition 9.1.12, p. 408 (new in the 2021 edition), locally**: two labelled
local branching structures at `x` have the same dimensional parts near `x`, under the graph
representation at the points of `supp(Θ)`; no branched hypothesis on `Θ` is used. -/
theorem dimPartsAgreeNear_of_hasGraphChartAt (hG : ∀ y ∈ supp Θ, X.PObj.HasGraphChartAt y)
    (B B' : X.LocalBranchingStructure Θ x) {dim : B.ι → ℕ} {dim' : B'.ι → ℕ}
    (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i))
    (hdim' : ∀ j, X.PObj.IsSubmanifoldOfDim (B'.M j) (dim' j)) :
    DimPartsAgreeNear B B' dim dim' :=
  dimPartsAgreeNear_of_topMultiplicityAt_aux _ Θ
    (fun y hy k => MPolyfold.topMultiplicityAt_of_hasGraphChartAt (hG y hy) k) B B' dim dim'
    hdim hdim' rfl

end LocalBranchingStructure

/-- **2021 Proposition 9.1.12, p. 408**, under the graph representation at every point. -/
theorem proposition_9_1_12_of_hasGraphChartAt (hG : ∀ y, X.PObj.HasGraphChartAt y) :
    X.Proposition_9_1_12 := fun _ _ _ B B' _ _ hdim hdim' =>
  LocalBranchingStructure.dimPartsAgreeNear_of_hasGraphChartAt (fun y _ => hG y) B B' hdim hdim'

/-- **2021 Lemma 9.6.4, p. 455**, under the graph representation at every point. -/
theorem LocalBranchingStructure.lemma_9_6_4_of_hasGraphChartAt
    (hG : ∀ y, X.PObj.HasGraphChartAt y) {x : Obj} {B B' : X.LocalBranchingStructure Θ x}
    {dim : B.ι → ℕ} {dim' : B'.ι → ℕ}
    (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i))
    (hdim' : ∀ j, X.PObj.IsSubmanifoldOfDim (B'.M j) (dim' j)) {y : Obj} (hyU : y ∈ B.U)
    (hyU' : y ∈ B'.U) : B.IsTopGoodPoint dim y ↔ B'.IsTopGoodPoint dim' y :=
  lemma_9_6_4 (MPolyfold.topMultiplicity_of_hasGraphChartAt hG _) hdim hdim' hyU hyU'

end EpGroupoid

namespace EpGroupoid

variable {m : ℕ} {Mor : Type} [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {X : EpGroupoid (Fin m → ℝ) Mor}

/-- **2021 Proposition 9.1.12, p. 408, over `ℝᵐ`**, for every `m` and every dimension, with no
hypothesis. -/
theorem proposition_9_1_12_rn (hX : X.PObj = rnPolyfold m) : X.Proposition_9_1_12 :=
  proposition_9_1_12_of_hasGraphChartAt fun y => hX ▸ MPolyfold.hasGraphChartAt_rn y

/-- **2021 Proposition 9.1.12** for the trivial ep-groupoid of `ℝᵐ`. -/
theorem proposition_9_1_12_trivial_rn : (trivial (rnPolyfold m)).Proposition_9_1_12 :=
  proposition_9_1_12_rn rfl

end EpGroupoid

/-! ### Local constancy of the dimension in `ℝᵐ`, labelled restrictions, Theorem 9.2.1 -/

namespace MPolyfold

open scoped ContDiff

variable {m : ℕ}

/-- `rn_exists_retraction` with the chart tangent spaces at every point of `W ∩ A`. -/
theorem rn_exists_retraction_forall {A : Set (Fin m → ℝ)}
    (hA : (rnPolyfold m).IsSmoothSubmanifold A) {x : Fin m → ℝ} (hx : x ∈ A) :
    ∃ W : Set (Fin m → ℝ), IsOpen W ∧ x ∈ W ∧ ∃ s : (Fin m → ℝ) → Fin m → ℝ,
      ContDiffOn ℝ ∞ s W ∧ MapsTo s W W ∧ (∀ y ∈ W, s (s y) = s y) ∧ s '' W = W ∩ A ∧
      ∀ y ∈ W ∩ A,
        (rnPolyfold m).chartTangent (isChart_rnChart 0) A y = range (fderiv ℝ s y) := by
  obtain ⟨d, hxV⟩ := isSmoothSubmanifold_iff.1 hA x hx
  have hφ : (rnPolyfold m).IsChart (rnChart m 0) := isChart_rnChart 0
  set W := d.toSubData.shrink (rnChart m 0) with hWdef
  have hWo : IsOpen W := d.toSubData.isOpen_shrink _
  have hxW : x ∈ W := d.toSubData.mem_shrink _ hx hxV (mem_univ x)
  have hmaps : MapsTo d.s W W := d.toSubData.mapsTo_shrink _
  have hU : IsRelOpenInQuadrant (rnSc m) univ W :=
    ⟨isPartialQuadrant_univ _, W, hWo, (inter_univ _).symm⟩
  have hsm := d.isScPlusRetractionOn.isScSmoothOn.smooth (rnChart m 0) (rnChart m 0) hφ hφ W hWo
    (fun y hy => ⟨d.toSubData.shrink_subset_V _ hy, mem_univ y⟩) (fun y _ => mem_univ _)
  have hR : (ScRetraction.id hU).retract = (rnChart m 0) '' W := by
    rw [rnChart_zero_image]; exact image_id W
  have h1 := hsm.comp_isScSmooth (ScRetraction.id hU) hR
  have h2' := (isScSmooth_iff_contDiffOn_const (V := Fin m → ℝ) (W := Fin m → ℝ) hU.isScDomain
    (((rnChart m 0) ∘ d.s ∘ (rnChart m 0).symm) ∘ (ScRetraction.id hU))).1 h1
  have h2 : ContDiffOn ℝ ∞ d.s W := h2'.congr fun y _ => by
    change d.s y = d.s (y + 0) - 0
    rw [add_zero, sub_zero]
  have hidem : ∀ y ∈ W, d.s (d.s y) = d.s y := fun y hy =>
    d.isScPlusRetractionOn.idem y (d.toSubData.shrink_subset_V _ hy)
  have himg : d.s '' W = W ∩ A := d.toSubData.image_shrink _
  refine ⟨W, hWo, hxW, d.s, h2, hmaps, hidem, himg, fun y hy => ?_⟩
  have hyV : y ∈ d.V := d.toSubData.shrink_subset_V _ hy.1
  let R : ScRetraction (rnSc m) univ := ⟨W, d.s, hU, hmaps,
    (isScSmooth_iff_contDiffOn_const (V := Fin m → ℝ) (W := Fin m → ℝ) hU.isScDomain d.s).2 h2,
    hidem⟩
  have hRr : R.retract = W ∩ A := himg
  have hset : (rnChart m 0) '' (W ∩ A) = R.retract := by rw [rnChart_zero_image, hRr]
  have hy1 : y ∈ (rnPolyfold m).levelSet 1 := by rw [rnPolyfold_levelSet]; exact mem_univ y
  have hl : (rnChart m 0).model.E.toBase 1 (levelLift (rnChart m 0) 1 y) = rnChart m 0 y :=
    (rnPolyfold m).toBase_levelLift hφ (mem_univ y) hy1
  have hl' : (levelLift (rnChart m 0) 1 y : Fin m → ℝ) = y := by
    rw [rnChart_zero_apply'] at hl
    exact (ScBanach.const_toBase (Fin m → ℝ) 1 _).symm.trans hl
  have hz : (y : (rnSc m) 1) ∈ (rnSc m).lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, ScBanach.const_toBase, hRr]; exact hy
  have hd : HasFDerivWithinAt d.s (scDeriv (E := rnSc m) (F := rnSc m) W d.s y) W y :=
    hasFDerivWithinAt_scDeriv_const' (V := Fin m → ℝ) (F := rnSc m) (U := W) (f := d.s)
      R.isSc1 hy.1
  have hfd : fderiv ℝ d.s y = scDeriv (E := rnSc m) (F := rnSc m) W d.s y :=
    (hd.hasFDerivAt (hWo.mem_nhds hy.1)).fderiv
  rw [chartTangent_eq hφ d hy.2 hyV (mem_univ y)]
  have hl'' : levelLift (rnChart m 0) 1 y = (show (rnChart m 0).model.E 1 from y) := hl'
  rw [hl'']
  erw [hset, tangentSpace_eq_range R hz, hfd]

/-- **Local constancy of the dimension at `x`** (2021 Remark 9.1.1, p. 402): every smooth
finite-dimensional submanifold through `x` has constant dimension near `x`. -/
def HasLocallyConstantDimAt {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) (x : X) : Prop :=
  ∀ A : Set X, P.IsSmoothSubmanifold A → x ∈ A →
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ n, P.IsSubmanifoldOfDim (A ∩ V) n

/-- **Remark 9.1.1 in `ℝᵐ`**: the dimension of a submanifold is locally constant.  For the
retraction `s` with `s(W) = W ∩ A`, `T_yA = range Ds(y)` and `Ds(y)` is a projection, so
`dim T_yA = trace Ds(y)`, continuous in `y` and integer-valued. -/
theorem hasLocallyConstantDimAt_rn (x : Fin m → ℝ) : (rnPolyfold m).HasLocallyConstantDimAt x := by
  intro A hA hx
  obtain ⟨n, hn⟩ := hA.exists_hasDimAt hx
  obtain ⟨W, hWo, hxW, s, hsm, -, hidem, himg, hT⟩ := rn_exists_retraction_forall hA hx
  have hfix : ∀ a ∈ W ∩ A, s a = a := fun a ha => by
    rw [← himg] at ha
    obtain ⟨w, hw, rfl⟩ := ha
    exact hidem w hw
  set fr : (Fin m → ℝ) → ℕ := fun y =>
    finrank ℝ (LinearMap.range (fderiv ℝ s y : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))) with hfrdef
  have hdimy : ∀ y ∈ W ∩ A, (rnPolyfold m).HasDimAt A y (fr y) := fun y hy => by
    obtain ⟨k, hk⟩ := hA.exists_hasDimAt hy.2
    have h := finrank_chartTangent (isChart_rnChart 0) hk hA (mem_univ y)
      (N := LinearMap.range (fderiv ℝ s y : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)))
      (by rw [hT y hy]; rfl)
    have hfk : fr y = k := h
    rw [hfk]; exact hk
  let tr : ((Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) →ₗ[ℝ] ℝ :=
    (LinearMap.trace ℝ (Fin m → ℝ)).comp (ContinuousLinearMap.coeLM ℝ)
  have htr_cont : Continuous tr := LinearMap.continuous_of_finiteDimensional tr
  have htr : ∀ y ∈ W ∩ A, tr (fderiv ℝ s y) = fr y := fun y hy => by
    obtain ⟨-, hDfix⟩ := rn_retraction_deriv hWo hy.1 hsm hidem (hfix y hy)
    have hid : IsIdempotentElem (fderiv ℝ s y : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) := by
      refine LinearMap.ext fun v => ?_
      exact hDfix _ ⟨v, rfl⟩
    exact ((LinearMap.isProj_range_iff_isIdempotentElem _).2 hid).trace
  have hcont : ContinuousAt (fun y => tr (fderiv ℝ s y)) x :=
    htr_cont.continuousAt.comp ((hsm.continuousOn_fderiv_of_isOpen hWo (by simp)).continuousAt
      (hWo.mem_nhds hxW))
  have hnb := hcont (Metric.ball_mem_nhds (tr (fderiv ℝ s x)) one_half_pos)
  obtain ⟨V, hVsub, hVo, hxV⟩ := mem_nhds_iff.1 hnb
  have hnx : n = fr x := hn.unique (hdimy x ⟨hxW, hx⟩)
  refine ⟨W ∩ V, hWo.inter hVo, ⟨hxW, hxV⟩, n, hA.inter_isOpen (hWo.inter hVo), fun a ha => ?_⟩
  refine (hasDimAt_inter_isOpen_iff hA (hWo.inter hVo) ha.2).2 ?_
  have ha' : a ∈ W ∩ A := ⟨ha.2.1, ha.1⟩
  have hball : dist (tr (fderiv ℝ s a)) (tr (fderiv ℝ s x)) < 1 / 2 := hVsub ha.2.2
  rw [htr a ha', htr x ⟨hxW, hx⟩, Real.dist_eq, abs_lt] at hball
  have h1 : (fr a : ℝ) < fr x + 1 := by linarith
  have h2 : (fr x : ℝ) < fr a + 1 := by linarith
  have h1' : fr a < fr x + 1 := by exact_mod_cast h1
  have h2' : fr x < fr a + 1 := by exact_mod_cast h2
  have hax : fr a = fr x := by omega
  rw [hnx, ← hax]
  exact hdimy a ha'

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ}

namespace LocalBranchingStructure

variable {x : Obj}

/-- The restriction of a local branching structure (Symmetric.lean) has the same tangent sum. -/
theorem tangentSum_restrict (B : X.LocalBranchingStructure Θ x) {V : Set Obj} (hV : IsOpen V)
    (hxV : x ∈ V) (hVU : V ⊆ B.U) : (B.restrict hV hxV hVU).tangentSum = B.tangentSum := by
  unfold tangentSum
  refine Finset.sum_congr rfl fun i _ => ?_
  change Finsupp.single (X.PObj.submanifoldTangent (B.M i ∩ V) x) (B.σ i) = _
  rw [MPolyfold.submanifoldTangent_inter_isOpen hV hxV]

/-- **A restriction with dimension labels**, under local constancy of the dimension at `x`
(2021 Remark 9.1.1, p. 402). -/
theorem exists_restrict_labelled (B : X.LocalBranchingStructure Θ x)
    (hLC : X.PObj.HasLocallyConstantDimAt x) :
    ∃ (V : Set Obj) (hV : IsOpen V) (hxV : x ∈ V) (hVU : V ⊆ B.U) (dim : B.ι → ℕ),
      ∀ i, X.PObj.IsSubmanifoldOfDim ((B.restrict hV hxV hVU).M i) (dim i) := by
  have h := fun i => hLC (B.M i) (B.isSmoothSubmanifold i) (B.mem_M i)
  choose W hW hxW dim hdim using h
  refine ⟨B.U ∩ ⋂ i, W i, B.isOpen_U.inter (isOpen_iInter_of_finite hW),
    ⟨B.mem_U, mem_iInter.2 hxW⟩, inter_subset_left, dim, fun i => ?_⟩
  have hset : B.M i ∩ (B.U ∩ ⋂ i, W i) = (B.M i ∩ W i) ∩ (B.U ∩ ⋂ i, W i) := by
    ext y
    simp only [mem_inter_iff, mem_iInter]
    exact ⟨fun h => ⟨⟨h.1, h.2.2 i⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
  change X.PObj.IsSubmanifoldOfDim (B.M i ∩ (B.U ∩ ⋂ i, W i)) (dim i)
  rw [hset]
  exact (hdim i).inter_isOpen (B.isOpen_U.inter (isOpen_iInter_of_finite hW))

end LocalBranchingStructure

/-- **2021 Theorem 9.2.1, p. 409 (2017: Theorem 9.1, p. 298), independence of the tangent
sums**, for labelled structures of any dimensions, under the graph representation on `supp(Θ)`
(through `hasIndependentTangentSums_of_dimPartsAgreeNear` of `Tangent.lean`). -/
theorem hasIndependentTangentSums_of_hasGraphChartAt
    (hlab : ∀ (x : Obj) (B : X.LocalBranchingStructure Θ x),
      ∃ dim : B.ι → ℕ, ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i))
    (hG : ∀ x ∈ supp Θ, X.PObj.HasGraphChartAt x) : X.HasIndependentTangentSums Θ :=
  hasIndependentTangentSums_of_dimPartsAgreeNear (fun x B B' _ => by
    obtain ⟨dim, hdim⟩ := hlab x B
    obtain ⟨dim', hdim'⟩ := hlab x B'
    exact ⟨dim, dim', hdim, hdim',
      LocalBranchingStructure.dimPartsAgreeNear_of_hasGraphChartAt hG B B' hdim hdim'⟩)
    fun x hx n => MPolyfold.hasTangentSlicesAt_of_hasGraphChartsAt ((hG x hx).hasGraphChartsAt n)

/-- **2021 Theorem 9.2.1, p. 409, independence of the tangent sums**, without labels: under the
graph representation and local constancy of the dimension on `supp(Θ)`. -/
theorem hasIndependentTangentSums_of_hasGraphChartAt_of_hasLocallyConstantDimAt
    (hG : ∀ x ∈ supp Θ, X.PObj.HasGraphChartAt x)
    (hLC : ∀ x ∈ supp Θ, X.PObj.HasLocallyConstantDimAt x) : X.HasIndependentTangentSums Θ := by
  intro x B B'
  by_cases hx : x ∈ supp Θ
  · obtain ⟨V, hV, hxV, hVU, dim, hdim⟩ := B.exists_restrict_labelled (hLC x hx)
    obtain ⟨V', hV', hxV', hVU', dim', hdim'⟩ := B'.exists_restrict_labelled (hLC x hx)
    rw [← B.tangentSum_restrict hV hxV hVU, ← B'.tangentSum_restrict hV' hxV' hVU']
    exact (B.restrict hV hxV hVU).tangentSum_eq_of_dimPartsAgreeNear
      (B'.restrict hV' hxV' hVU') hdim hdim'
      (LocalBranchingStructure.dimPartsAgreeNear_of_hasGraphChartAt hG _ _ hdim hdim')
      fun n => MPolyfold.hasTangentSlicesAt_of_hasGraphChartsAt ((hG x hx).hasGraphChartsAt n)
  · rw [B.tangentSum_eq_zero hx, B'.tangentSum_eq_zero hx]

end EpGroupoid

namespace EpGroupoid

variable {m : ℕ} {Mor : Type} [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {X : EpGroupoid (Fin m → ℝ) Mor}

/-- **2021 Theorem 9.2.1, p. 409, independence of the tangent sums over `ℝᵐ`**, for every `Θ`
(not necessarily equidimensional, not necessarily branched), with no hypothesis. -/
theorem hasIndependentTangentSums_rn (hX : X.PObj = rnPolyfold m) (Θ : (Fin m → ℝ) → ℚ) :
    X.HasIndependentTangentSums Θ :=
  hasIndependentTangentSums_of_hasGraphChartAt_of_hasLocallyConstantDimAt
    (fun y _ => hX ▸ MPolyfold.hasGraphChartAt_rn y)
    (fun y _ => hX ▸ MPolyfold.hasLocallyConstantDimAt_rn y)

end EpGroupoid

/-! ### Proposition 9.6.5 and the formula of p. 457 -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ}

namespace LocalBranchingStructure

variable {x : Obj}

open scoped Classical in
/-- **A top slice of the class `T`** (the points `x^e` of 2021 Proposition 9.6.5, p. 456): a
finite set of points of `U` off the lower-dimensional sheets, meeting each top sheet with tangent
space `T` in exactly one point and no other top sheet. -/
def IsTopSlice (B : X.LocalBranchingStructure Θ x) (dim : B.ι → ℕ)
    (T : Set X.PObj.TangentSpace) (S : Finset Obj) : Prop :=
  (∀ y ∈ S, y ∈ B.U ∧ ∀ i, dim i < B.topDim dim → y ∉ B.M i) ∧
    ∀ i, dim i = B.topDim dim →
      (X.PObj.submanifoldTangent (B.M i) x = T → ∃! y, y ∈ S ∧ y ∈ B.M i) ∧
      (X.PObj.submanifoldTangent (B.M i) x ≠ T → ∀ y ∈ S, y ∉ B.M i)

open scoped Classical in
/-- **2021 Proposition 9.6.5, p. 456 (new in the 2021 edition), slice form**: for a top class
(the class of `i₀`) and every open `W ∋ x` there is a top slice in `W` on the sheets of the
class.  The sets `I^e` of the text are the indices of the sheets through its points. -/
theorem proposition_9_6_5 (B : X.LocalBranchingStructure Θ x) {dim : B.ι → ℕ}
    (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i)) (hG : X.PObj.HasGraphChartAt x)
    {i₀ : B.ι} (hi₀ : dim i₀ = B.topDim dim) {W : Set Obj} (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ S : Finset Obj, (∀ y ∈ S, y ∈ W ∧ ∃ i, dim i = B.topDim dim ∧
        X.PObj.submanifoldTangent (B.M i) x = X.PObj.submanifoldTangent (B.M i₀) x ∧
        y ∈ B.M i) ∧
      B.IsTopSlice dim (X.PObj.submanifoldTangent (B.M i₀) x) S := by
  set K := B.topDim dim
  have hA : ∀ i : {i // dim i = K}, X.PObj.IsSubmanifoldOfDim (B.M i.1) K := fun i =>
    (congrArg (X.PObj.IsSubmanifoldOfDim (B.M i.1)) i.2).mp (hdim i.1)
  obtain ⟨F, hFWO, hFL, hF⟩ := MPolyfold.exists_generic_slice hG (fun i : {i // dim i = K} =>
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
/-- The formula of 2021 p. 457 for one class: its weight is `∑_{y ∈ S} Θ(y)`. -/
theorem sum_class_eq_sum_of_isTopSlice (B : X.LocalBranchingStructure Θ x) {dim : B.ι → ℕ}
    {T : Set X.PObj.TangentSpace} {S : Finset Obj} (hS : B.IsTopSlice dim T S) :
    ∑ i with dim i = B.topDim dim ∧ X.PObj.submanifoldTangent (B.M i) x = T, B.σ i =
      ∑ y ∈ S, Θ y := by
  rw [Finset.sum_congr rfl fun y hy => B.eq_sum y (hS.1 y hy).1]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : dim i = B.topDim dim
  · by_cases hc : X.PObj.submanifoldTangent (B.M i) x = T
    · rw [if_pos ⟨hi, hc⟩]
      obtain ⟨y₀, ⟨hy₀S, hy₀i⟩, hy₀⟩ := ((hS.2 i hi).1 hc)
      rw [Finset.sum_eq_single y₀ (fun y hyS hne => if_neg fun hyi => hne (hy₀ y ⟨hyS, hyi⟩))
        (fun h => (h hy₀S).elim), if_pos hy₀i]
    · rw [if_neg fun h => hc h.2]
      exact (Finset.sum_eq_zero fun y hy => if_neg ((hS.2 i hi).2 hc y hy)).symm
  · rw [if_neg fun h => hi h.1]
    have hlt : dim i < B.topDim dim := lt_of_le_of_ne (B.dim_le_topDim dim i) hi
    exact (Finset.sum_eq_zero fun y hy => if_neg ((hS.1 y hy).2 i hlt)).symm

open scoped Classical in
/-- **The formula of 2021 p. 457**: `Θ_k(x) = ∑_Ξ ∑_e Θ(x^e)` for top slices of all
classes. -/
theorem dimPart_topDim_eq_sum_slices (B : X.LocalBranchingStructure Θ x) {dim : B.ι → ℕ}
    (Ts : Finset (Set X.PObj.TangentSpace))
    (hTs : ∀ i, dim i = B.topDim dim → X.PObj.submanifoldTangent (B.M i) x ∈ Ts)
    (S : Set X.PObj.TangentSpace → Finset Obj) (hS : ∀ T ∈ Ts, B.IsTopSlice dim T (S T)) :
    B.dimPart dim (B.topDim dim) x = ∑ T ∈ Ts, ∑ y ∈ S T, Θ y := by
  have h1 : B.dimPart dim (B.topDim dim) x = ∑ i with dim i = B.topDim dim, B.σ i := by
    unfold dimPart
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext i
    simp [B.mem_M i]
  rw [h1, ← Finset.sum_fiberwise_of_maps_to (g := fun i => X.PObj.submanifoldTangent (B.M i) x)
    (t := Ts) (fun i hi => hTs i (Finset.mem_filter.1 hi).2)]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [← sum_class_eq_sum_of_isTopSlice B (hS T hT), Finset.filter_filter]

open scoped Classical in
/-- **The class weights do not depend on the structure** (2021 p. 457), under the graph
representation at `x`: one slice for the sheets of both structures. -/
theorem sum_class_eq_of_hasGraphChartAt (hG : X.PObj.HasGraphChartAt x)
    {B B' : X.LocalBranchingStructure Θ x} {dim : B.ι → ℕ} {dim' : B'.ι → ℕ}
    (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i))
    (hdim' : ∀ j, X.PObj.IsSubmanifoldOfDim (B'.M j) (dim' j)) (T : Set X.PObj.TangentSpace) :
    ∑ i with dim i = B.topDim dim ∧ X.PObj.submanifoldTangent (B.M i) x = T, B.σ i =
      ∑ j with dim' j = B'.topDim dim' ∧ X.PObj.submanifoldTangent (B'.M j) x = T, B'.σ j := by
  have hK : B'.topDim dim' = B.topDim dim := (lemma_9_6_1 hdim hdim').symm
  rw [hK]
  set K := B.topDim dim
  have hO : IsOpen (B.U ∩ B'.U) := B.isOpen_U.inter B'.isOpen_U
  have key := MPolyfold.sum_class_eq_of_hasGraphChartAt hG hO ⟨B.mem_U, B'.mem_U⟩
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

/-- **`Θ_k(x)` does not depend on the structure** (the conclusion of 2021 p. 457), under the
graph representation at `x`. -/
theorem dimPart_topDim_eq_of_hasGraphChartAt (hG : X.PObj.HasGraphChartAt x)
    {B B' : X.LocalBranchingStructure Θ x} {dim : B.ι → ℕ} {dim' : B'.ι → ℕ}
    (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i))
    (hdim' : ∀ j, X.PObj.IsSubmanifoldOfDim (B'.M j) (dim' j)) :
    B.dimPart dim (B.topDim dim) x = B'.dimPart dim' (B'.topDim dim') x :=
  dimPart_topDim_eq_of_topMultiplicityAt
    (fun _ => MPolyfold.topMultiplicityAt_of_hasGraphChartAt hG _) hdim hdim' B.mem_U B'.mem_U

end LocalBranchingStructure

end EpGroupoid

/-! ### A mixed-dimensional witness in `ℝ²` -/

namespace EpGroupoid

open scoped Classical in
/-- The counting function of the graphs of `γ₁`, `γ₂` and `{0}` in `ℝ²`. -/
theorem sum_three_eq (γ₁ γ₂ : ℝ → ℝ) (y : Fin 2 → ℝ) :
    (∑ i with y ∈ ![graph2 γ₁, graph2 γ₂, ({0} : Set (Fin 2 → ℝ))] i, (1 : ℚ)) =
      thetaGraphs γ₁ γ₂ y + if y = 0 then 1 else 0 := by
  rw [Finset.sum_filter, Fin.sum_univ_three, thetaGraphs_apply]
  congr 1
  all_goals exact if_congr Iff.rfl rfl rfl

namespace Remark913Hyp

variable {β₁ β₂ : ℝ → ℝ} (h : Remark913Hyp β₁ β₂)
include h

open scoped Classical in
/-- **A mixed-dimensional witness for 2021 Proposition 9.1.12 and Theorem 9.2.1 in `ℝ²`**: the
`Θ` of 2021 Remark 9.1.3 (b) plus `δ₀` has two labelled structures with sheets of dimensions
`1` and `0` (the graphs of `β₁`, `β₂` and of `0`, `β₁ + β₂`, and `{0}`); their dimensional parts
agree near `0` and their tangent sums agree. -/
theorem exists_mixed_rn_two :
    ∃ (Θ : (Fin 2 → ℝ) → ℚ) (B B' : (trivial (rnPolyfold 2)).LocalBranchingStructure Θ 0)
      (dim : B.ι → ℕ) (dim' : B'.ι → ℕ),
      (trivial (rnPolyfold 2)).IsBranchedEpSubgroupoid Θ ∧
      (∀ i, (rnPolyfold 2).IsSubmanifoldOfDim (B.M i) (dim i)) ∧
      (∀ j, (rnPolyfold 2).IsSubmanifoldOfDim (B'.M j) (dim' j)) ∧
      (∃ i, dim i = 0) ∧ (∃ i, dim i = 1) ∧
      (∀ i, ∃ s, B.M i = ![graph2 β₁, graph2 β₂, ({0} : Set (Fin 2 → ℝ))] s ∩ B.U) ∧
      (∀ j, ∃ s, B'.M j = ![graph2 0, graph2 (β₁ + β₂), ({0} : Set (Fin 2 → ℝ))] s ∩ B'.U) ∧
      LocalBranchingStructure.DimPartsAgreeNear B B' dim dim' ∧
      B.tangentSum = B'.tangentSum := by
  set M : Fin 3 → Set (Fin 2 → ℝ) := ![graph2 β₁, graph2 β₂, {0}] with hMdef
  set M' : Fin 3 → Set (Fin 2 → ℝ) := ![graph2 0, graph2 (β₁ + β₂), {0}] with hM'def
  have hMd : ∀ i, (rnPolyfold 2).IsSubmanifoldOfDim (M i) (![1, 1, 0] i) := by
    intro i
    fin_cases i
    · exact rnPolyfold_isSubmanifoldOfDim_graph2 h.contDiff₁
    · exact rnPolyfold_isSubmanifoldOfDim_graph2 h.contDiff₂
    · exact rnPolyfold_isSubmanifoldOfDim_singleton 0
  have hM'd : ∀ i, (rnPolyfold 2).IsSubmanifoldOfDim (M' i) (![1, 1, 0] i) := by
    intro i
    fin_cases i
    · exact rnPolyfold_isSubmanifoldOfDim_graph2 contDiff_const
    · exact rnPolyfold_isSubmanifoldOfDim_graph2 (h.contDiff₁.add h.contDiff₂)
    · exact rnPolyfold_isSubmanifoldOfDim_singleton 0
  have hc : ∀ i, IsClosed (M i) := by
    intro i
    fin_cases i
    · exact isClosed_graph2 h.contDiff₁.continuous
    · exact isClosed_graph2 h.contDiff₂.continuous
    · exact isClosed_singleton
  have hc' : ∀ i, IsClosed (M' i) := by
    intro i
    fin_cases i
    · exact isClosed_graph2 continuous_const
    · exact isClosed_graph2 (h.contDiff₁.continuous.add h.contDiff₂.continuous)
    · exact isClosed_singleton
  have hΘ : ∀ y, (∑ i with y ∈ M' i, (1 : ℚ)) = ∑ i with y ∈ M i, (1 : ℚ) := fun y => by
    rw [hMdef, hM'def, sum_three_eq, sum_three_eq, thetaGraphs_eq h.eq_zero_or y]
  set B := localBranchingStructure_sum_rn M 1 (fun _ => one_pos) (fun i => (hMd i).1) hc 0
  set B' := (localBranchingStructure_sum_rn M' 1 (fun _ => one_pos) (fun i => (hM'd i).1) hc'
    0).ofEq hΘ
  have h10 : β₁ 0 = 0 := h.eq_zero₁ 0 le_rfl
  have h20 : β₂ 0 = 0 := h.eq_zero₂ 0 le_rfl
  have h0M : ∀ i, (0 : Fin 2 → ℝ) ∈ M i := by
    intro i
    fin_cases i
    · change (0 : Fin 2 → ℝ) 1 = β₁ ((0 : Fin 2 → ℝ) 0); simp [h10]
    · change (0 : Fin 2 → ℝ) 1 = β₂ ((0 : Fin 2 → ℝ) 0); simp [h20]
    · exact mem_singleton _
  refine ⟨_, B, B', fun i => ![1, 1, 0] i.1, fun j => ![1, 1, 0] j.1,
    isBranchedEpSubgroupoid_sum_rn M 1 (fun _ => one_pos) (fun i => (hMd i).1) hc,
    fun i => (hMd i.1).inter_isOpen B.isOpen_U, fun j => (hM'd j.1).inter_isOpen B'.isOpen_U,
    ⟨⟨2, h0M 2⟩, rfl⟩, ⟨⟨0, h0M 0⟩, rfl⟩, fun i => ⟨i.1, rfl⟩, fun j => ⟨j.1, rfl⟩,
    proposition_9_1_12_trivial_rn _ (isBranchedEpSubgroupoid_sum_rn M 1 (fun _ => one_pos)
      (fun i => (hMd i).1) hc) 0 B B' _ _ (fun i => (hMd i.1).inter_isOpen B.isOpen_U)
      (fun j => (hM'd j.1).inter_isOpen B'.isOpen_U),
    hasIndependentTangentSums_rn rfl _ 0 B B'⟩

end Remark913Hyp

end EpGroupoid

/-! ### Definition 9.2.12: `TMᵢ` is a sub-M-polyfold of `TX` -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

namespace SubmanifoldData

variable {A : Set X} (d : P.SubmanifoldData A)

/-- `Ts` maps `TV` to `TV`. -/
theorem mapsTo_tmap : MapsTo d.tmap (P.tangentPreimage d.V) (P.tangentPreimage d.V) :=
  fun α hα => by
    change P.levelVal 1 (P.tangentProj (d.tmap α)) ∈ d.V
    rw [d.levelVal_tangentProj_tmap hα]
    exact d.isScPlusRetractionOn.mapsTo hα

/-- `Ts(TV) = TA ∩ TV`: the image of `Ts` consists of the vectors `h` with `h ∈ T_{p(h)}A`. -/
theorem image_tmap :
    d.tmap '' P.tangentPreimage d.V =
      {α | α ∈ P.submanifoldTangent A (P.levelVal 1 (P.tangentProj α))} ∩
        P.tangentPreimage d.V := by
  ext β
  constructor
  · rintro ⟨α, hα, rfl⟩
    refine ⟨?_, d.mapsTo_tmap hα⟩
    change d.tmap α ∈ P.submanifoldTangent A (P.levelVal 1 (P.tangentProj (d.tmap α)))
    rw [d.levelVal_tangentProj_tmap hα]
    exact d.tmap_mem_submanifoldTangent hα
  · rintro ⟨hβA, hβV⟩
    exact ⟨β, hβV, ((mem_submanifoldTangent_iff d hβV).1 hβA).2⟩

end SubmanifoldData

/-- **`TA` is a sub-M-polyfold of `TX`** (Definition 2.20; for 2021 Definition 9.2.12, p. 418):
near each of its points it is the image of the sc-smooth retraction `Ts` of `TV`
(`tangentMapOn_isScSmoothOn`, `tmap_tmap`). -/
theorem IsSmoothSubmanifold.isSubMPolyfold_tangent {A : Set X} (hA : P.IsSmoothSubmanifold A) :
    P.tangentPolyfold.IsSubMPolyfold
      {α | α ∈ P.submanifoldTangent A (P.levelVal 1 (P.tangentProj α))} := by
  intro a ha
  obtain ⟨d, hyd⟩ := isSmoothSubmanifold_iff.1 hA _ (mem_of_mem_submanifoldTangent ha)
  exact ⟨P.tangentPreimage d.V, isOpen_tangentPreimage d.isOpen, hyd, d.tmap, d.mapsTo_tmap,
    tangentMapOn_isScSmoothOn d.isScPlusRetractionOn.isScSmoothOn, fun α hα => d.tmap_tmap hα,
    d.image_tmap⟩

variable (P) in
/-- Every point of `X₁` carries a tangent vector (the zero vector). -/
theorem exists_levelVal_tangentProj_eq {y : X} (hy : y ∈ P.levelSet 1) :
    ∃ α : P.TangentSpace, P.levelVal 1 (P.tangentProj α) = y := by
  obtain ⟨φ, hφ, hyφ⟩ := P.exists_isChart_mem_source y
  refine ⟨TangentSpace.mk ⟨y, φ, 0, hφ, hyφ, hy, mk_zero_mem_retractTangent φ.model.isScRetract ?_⟩,
    rfl⟩
  change φ.model.E.toBase 1 (levelLift φ 1 y) ∈ φ.model.O
  rw [P.toBase_levelLift hφ hyφ hy]
  exact φ.mapsTo_model y hyφ

/-- `T_yA` is nonempty for `y ∈ A ∩ X₁`. -/
theorem IsSmoothSubmanifold.exists_mem_submanifoldTangent {A : Set X}
    (hA : P.IsSmoothSubmanifold A) {y : X} (hyA : y ∈ A) (hy : y ∈ P.levelSet 1) :
    ∃ α, α ∈ P.submanifoldTangent A y := by
  obtain ⟨d, hyd⟩ := isSmoothSubmanifold_iff.1 hA y hyA
  obtain ⟨α, hα⟩ := P.exists_levelVal_tangentProj_eq hy
  have hαV : α ∈ P.tangentPreimage d.V := by change _ ∈ d.V; rw [hα]; exact hyd
  refine ⟨d.tmap α, ?_⟩
  have h := d.tmap_mem_submanifoldTangent hαV
  rwa [hα, d.apply_eq_self ⟨hyA, hyd⟩] at h

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ}

/-- **The `TMᵢ` of 2021 Definition 9.2.12, p. 418, are sub-M-polyfolds of `TX`** (the
retraction part of `TangentBranchingHyp.isSmoothSubmanifold`; the sc⁺ part is not shown). -/
theorem LocalBranchingStructure.isSubMPolyfold_tangentSubmanifold {x : Obj}
    (B : X.LocalBranchingStructure Θ x) (i : B.ι) :
    X.tangentEpGroupoid.PObj.IsSubMPolyfold (X.tangentSubmanifold (B.M i)) :=
  (B.isSmoothSubmanifold i).isSubMPolyfold_tangent

end EpGroupoid

/-- **Witness in `ℝ²`**: the tangent of the line `{r₁ = 0}` is a sub-M-polyfold of `T(ℝ²)`,
nonempty, and not all of `T(ℝ²)` (vectors over `(0, 1)` are not in it). -/
theorem rnPolyfold_isSubMPolyfold_tangent_graph2 :
    (rnPolyfold 2).tangentPolyfold.IsSubMPolyfold
        {α | α ∈ (rnPolyfold 2).submanifoldTangent (graph2 0)
          ((rnPolyfold 2).levelVal 1 ((rnPolyfold 2).tangentProj α))} ∧
      (∃ α, α ∈ (rnPolyfold 2).submanifoldTangent (graph2 0)
          ((rnPolyfold 2).levelVal 1 ((rnPolyfold 2).tangentProj α))) ∧
      ∃ α : (rnPolyfold 2).TangentSpace,
        α ∉ (rnPolyfold 2).submanifoldTangent (graph2 0)
          ((rnPolyfold 2).levelVal 1 ((rnPolyfold 2).tangentProj α)) := by
  have hA := rnPolyfold_isSmoothSubmanifold_graph2 (β := 0) contDiff_const
  have h1 : ∀ y : Fin 2 → ℝ, y ∈ (rnPolyfold 2).levelSet 1 := fun y => by
    rw [rnPolyfold_levelSet]; exact mem_univ y
  refine ⟨hA.isSubMPolyfold_tangent, ?_, ?_⟩
  · obtain ⟨α, hα⟩ := hA.exists_mem_submanifoldTangent (y := 0) (by simp [graph2]) (h1 0)
    exact ⟨α, by rwa [MPolyfold.levelVal_tangentProj_of_mem hα]⟩
  · obtain ⟨α, hα⟩ := (rnPolyfold 2).exists_levelVal_tangentProj_eq (h1 ![0, 1])
    refine ⟨α, fun h => ?_⟩
    have := MPolyfold.mem_of_mem_submanifoldTangent h
    rw [hα] at this
    simp [graph2] at this

namespace EpGroupoid

variable {m : ℕ} {Mor : Type} [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {X : EpGroupoid (Fin m → ℝ) Mor} {Θ : (Fin m → ℝ) → ℚ}

/-- **Definition 9.2.12 over `ℝᵐ`** (2021 p. 418; 2017: Definition 9.6, p. 306): for a branched
ep⁺-subgroupoid `Θ`, not necessarily equidimensional, `TΘ` is a branched ep⁺-subgroupoid of
`T(X, 𝐗)` if `|X|` is paracompact and the `TMᵢ` are smooth submanifolds of `TX`; the
independence of the tangent sums holds (`hasIndependentTangentSums_rn`). -/
theorem isBranchedEpSubgroupoid_tangentTheta_rn (hX : X.PObj = rnPolyfold m)
    (hΘ : X.IsBranchedEpSubgroupoid Θ) (hpar : X.HasParacompactOrbitSpace)
    (hsub : ∀ (x : Fin m → ℝ) (B : X.LocalBranchingStructure Θ x) (i : B.ι),
      X.tangentEpGroupoid.PObj.IsSmoothSubmanifold (X.tangentSubmanifold (B.M i))) :
    X.tangentEpGroupoid.IsBranchedEpSubgroupoid (X.tangentTheta Θ) :=
  isBranchedEpSubgroupoid_tangentTheta_of_isSmoothSubmanifold hΘ (hasIndependentTangentSums_rn hX Θ)
    hpar hsub

end EpGroupoid

end Polyfold
