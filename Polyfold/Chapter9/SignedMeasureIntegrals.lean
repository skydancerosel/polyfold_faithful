import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 9, §9.5:
measure-theoretic preparation for **(9.22)**, p. 441 (`dμ_τ = f̄ dμ_ω`).

# Integrals against a finite signed measure, and densities from local estimates

The integral of a bounded measurable function against a finite signed measure is Mathlib's
`∫ᵛ x in K, g x ∂<•s` (`MeasureTheory.VectorMeasure.integral`, the integral against a vector
measure for the pairing `(r, v) ↦ v • r`, with respect to the variation `|s|`).  We record:

* `setIntegral_eq_jordan`: it is `∫_K g ds⁺ − ∫_K g ds⁻` for the Jordan decomposition
  `s = s⁺ − s⁻` (`SignedMeasure.toJordanDecomposition`); more generally
  `setIntegral_sub_toSignedMeasure`: `∫_K g d(μ₁ − μ₂) = ∫_K g dμ₁ − ∫_K g dμ₂` for any two finite
  measures, so the integral does not depend on the decomposition;
* `setIntegral_const_eq`: `∫_K a ds = a · s(K)`;
* `abs_setIntegral_sub_le`: `|∫_K g ds − a · s(K)| ≤ ε · |s|(K)` when `|g − a| ≤ ε` on `K`;
* **`eq_setIntegral_of_estimate`**: if a second signed measure `t` satisfies, on the measurable
  subsets `A` of a measurable set `D`, `|t(A) − a s(A)| ≤ ε B(A)` whenever `|g − a| ≤ ε` on `A`,
  for a set function `B` additive on disjoint measurable subsets of `D`, then
  `t(K) = ∫_K g ds` for every measurable `K ⊆ D` (Riemann–Stieltjes sums over the partition of
  `K` by the values of `g`, and `ε → 0`);
* **`eq_setIntegral_of_local_estimate`**: on a compact space whose open sets are measurable, such
  estimates near every point give `t(K) = ∫_K g ds` for every measurable `K` (finite subcover).
-/

open Set Filter Topology MeasureTheory VectorMeasure ContinuousLinearMap

noncomputable section

namespace Polyfold

namespace SignedDensity

variable {α : Type*} [MeasurableSpace α]

/-- The variation `|s| = s⁺ + s⁻` of a (finite) signed measure is a finite measure. -/
instance isFiniteMeasure_variation (s : SignedMeasure α) : IsFiniteMeasure s.variation := by
  rw [← s.totalVariation_eq_variation]
  unfold SignedMeasure.totalVariation
  infer_instance

/-- A bounded measurable function is integrable against a finite signed measure. -/
theorem integrable_of_bound (s : SignedMeasure α) {g : α → ℝ} (hg : Measurable g) {R : ℝ}
    (hR : ∀ x, |g x| ≤ R) : s.Integrable g :=
  Integrable.of_bound hg.aestronglyMeasurable R
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hR x)

theorem integrableOn_of_bound (s : SignedMeasure α) {g : α → ℝ} (hg : Measurable g) {R : ℝ}
    (hR : ∀ x, |g x| ≤ R) (K : Set α) : s.IntegrableOn g K :=
  integrable_of_bound (s.restrict K) hg hR

/-- `∫_K a ds = a · s(K)`. -/
theorem setIntegral_const_eq (s : SignedMeasure α) (K : Set α) (a : ℝ) :
    ∫ᵛ _ in K, a ∂<•s = a * s K := by
  rw [VectorMeasure.setIntegral_const]
  change s K • a = a * s K
  rw [smul_eq_mul, mul_comm]

/-- **Independence of the decomposition**: for finite measures `μ₁, μ₂` and measurable `K`,
`∫_K g d(μ₁ − μ₂) = ∫_K g dμ₁ − ∫_K g dμ₂`. -/
theorem setIntegral_sub_toSignedMeasure (μ₁ μ₂ : Measure α) [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂] {g : α → ℝ} (hg : Measurable g) {R : ℝ} (hR : ∀ x, |g x| ≤ R)
    {K : Set α} (hK : MeasurableSet K) :
    ∫ᵛ x in K, g x ∂<•(μ₁.toSignedMeasure - μ₂.toSignedMeasure) =
      ∫ x in K, g x ∂μ₁ - ∫ x in K, g x ∂μ₂ := by
  have hR' : ∀ x, |K.indicator g x| ≤ max R 0 := fun x => by
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]; exact (hR x).trans (le_max_left _ _)
    · rw [indicator_of_notMem hx, abs_zero]; exact le_max_right _ _
  have hgK : Measurable (K.indicator g) := hg.indicator hK
  rw [← VectorMeasure.integral_indicator hK,
    integral_sub_vectorMeasure (integrable_of_bound _ hgK hR') (integrable_of_bound _ hgK hR'),
    integral_toSignedMeasure, integral_toSignedMeasure, MeasureTheory.integral_indicator hK,
    MeasureTheory.integral_indicator hK]

/-- **The integral against a signed measure through its Jordan decomposition**:
`∫_K g ds = ∫_K g ds⁺ − ∫_K g ds⁻`. -/
theorem setIntegral_eq_jordan (s : SignedMeasure α) {g : α → ℝ} (hg : Measurable g) {R : ℝ}
    (hR : ∀ x, |g x| ≤ R) {K : Set α} (hK : MeasurableSet K) :
    ∫ᵛ x in K, g x ∂<•s = ∫ x in K, g x ∂s.toJordanDecomposition.posPart -
      ∫ x in K, g x ∂s.toJordanDecomposition.negPart := by
  conv_lhs => rw [← s.toSignedMeasure_toJordanDecomposition]
  exact setIntegral_sub_toSignedMeasure _ _ hg hR hK

theorem norm_lsmul_flip : ‖(lsmul ℝ ℝ (E := ℝ)).flip‖ = 1 := by
  rw [opNorm_flip, opNorm_lsmul]

/-- **The integral against a signed measure, as an estimate**: if `|g − a| ≤ ε` on `K`, then
`|∫_K g ds − a · s(K)| ≤ ε · |s|(K)`. -/
theorem abs_setIntegral_sub_le (s : SignedMeasure α) {g : α → ℝ} (hg : Measurable g) {R : ℝ}
    (hR : ∀ x, |g x| ≤ R) {K : Set α} {a ε : ℝ}
    (h : ∀ x ∈ K, |g x - a| ≤ ε) :
    |∫ᵛ x in K, g x ∂<•s - a * s K| ≤ ε * s.variation.real K := by
  have hga : ∀ x, |g x - a| ≤ R + |a| := fun x =>
    (abs_sub _ _).trans (add_le_add (hR x) le_rfl)
  have hca : ∀ x, |(fun _ : α => a) x| ≤ |a| := fun _ => le_rfl
  have e1 : ∫ᵛ x in K, g x ∂<•s - a * s K = ∫ᵛ x in K, g x - a ∂<•s := by
    rw [← setIntegral_const_eq s K a, integral_fun_sub (integrableOn_of_bound s hg hR K)
      (integrableOn_of_bound s measurable_const hca K)]
  rw [e1, ← Real.norm_eq_abs]
  have h2 := norm_setIntegral_le_of_norm_le_const (μ := s) (s := K)
    (B := (lsmul ℝ ℝ (E := ℝ)).flip) (f := fun x => g x - a) (C := ε)
    fun x hx => by rw [Real.norm_eq_abs]; exact h x hx
  rwa [norm_lsmul_flip, mul_one] at h2

/-- A set function additive on disjoint measurable subsets of `D` is additive on finite
disjoint families of measurable subsets of `D`. -/
theorem sum_eq_of_additive {D : Set α} (φ : Set α → ℝ)
    (hφ : ∀ A A', MeasurableSet A → MeasurableSet A' → A ⊆ D → A' ⊆ D → Disjoint A A' →
      φ (A ∪ A') = φ A + φ A')
    {ι : Type*} (J : Finset ι) (P : ι → Set α) (hP : ∀ i ∈ J, MeasurableSet (P i))
    (hPD : ∀ i ∈ J, P i ⊆ D) (hd : (J : Set ι).PairwiseDisjoint P) :
    φ (⋃ i ∈ J, P i) = ∑ i ∈ J, φ (P i) := by
  classical
  have h0 : φ ∅ = 0 := by
    have := hφ ∅ ∅ MeasurableSet.empty MeasurableSet.empty (empty_subset _) (empty_subset _)
      (disjoint_empty _)
    rw [union_empty] at this
    linarith
  induction J using Finset.induction_on with
  | empty => simp [h0]
  | insert j J hj IH =>
    simp only [Finset.coe_insert, Finset.forall_mem_insert, Finset.set_biUnion_insert]
      at hP hPD hd ⊢
    rw [hφ _ _ hP.1 (Finset.measurableSet_biUnion _ hP.2) hPD.1
      (iUnion₂_subset fun i hi => hPD.2 i hi), Finset.sum_insert hj,
      IH hP.2 hPD.2 (hd.subset (subset_insert _ _))]
    simp only [disjoint_iUnion_right]
    exact fun i hi => hd (mem_insert _ _) (mem_insert_of_mem _ hi)
      (ne_of_mem_of_not_mem hi hj).symm

theorem eq_zero_of_forall_abs_le {a c : ℝ} (h : ∀ ε > 0, |a| ≤ ε * c) : a = 0 := by
  by_contra ha
  have ha' : 0 < |a| := abs_pos.2 ha
  have hc : 0 < c := by
    have := h 1 one_pos
    linarith
  have h2 := h (|a| / (2 * c)) (by positivity)
  have e : |a| / (2 * c) * c = |a| / 2 := by field_simp
  linarith

/-- The pieces `K ∩ g⁻¹[−R + kε, −R + (k+1)ε)`. -/
def piece (g : α → ℝ) (R ε : ℝ) (K : Set α) (k : ℕ) : Set α :=
  K ∩ g ⁻¹' Ico (-R + k * ε) (-R + (k + 1) * ε)

omit [MeasurableSpace α] in
theorem eq_floor_of_mem_piece {g : α → ℝ} {R ε : ℝ} (hε : 0 < ε) {K : Set α} {k : ℕ} {x : α}
    (hx : x ∈ piece g R ε K k) : k = ⌊(g x + R) / ε⌋₊ := by
  obtain ⟨-, h1, h2⟩ := hx
  symm
  rw [Nat.floor_eq_iff]
  · constructor
    · rw [le_div_iff₀ hε]; linarith
    · rw [div_lt_iff₀ hε]; linarith
  · have : (0 : ℝ) ≤ k * ε := mul_nonneg (Nat.cast_nonneg _) hε.le
    exact div_nonneg (by linarith) hε.le

omit [MeasurableSpace α] in
theorem biUnion_piece {g : α → ℝ} {R ε : ℝ} (hε : 0 < ε) (hR : ∀ x, |g x| ≤ R) (K : Set α) :
    ⋃ k ∈ Finset.range (⌈2 * R / ε⌉₊ + 1), piece g R ε K k = K := by
  refine Subset.antisymm (iUnion₂_subset fun k _ => inter_subset_left) fun x hx => ?_
  have hb := abs_le.1 (hR x)
  have h0 : 0 ≤ (g x + R) / ε := div_nonneg (by linarith) hε.le
  refine mem_iUnion₂.2 ⟨⌊(g x + R) / ε⌋₊, Finset.mem_range.2 ?_, hx, ?_, ?_⟩
  · have h1 : ((⌊(g x + R) / ε⌋₊ : ℕ) : ℝ) ≤ 2 * R / ε :=
      (Nat.floor_le h0).trans (div_le_div_of_nonneg_right (by linarith) hε.le)
    have h2 := Nat.le_ceil (2 * R / ε)
    exact Nat.lt_succ_of_le (by exact_mod_cast h1.trans h2)
  · have := Nat.floor_le h0
    rw [le_div_iff₀ hε] at this
    linarith
  · have := Nat.lt_floor_add_one ((g x + R) / ε)
    rw [div_lt_iff₀ hε] at this
    linarith

omit [MeasurableSpace α] in
theorem pairwiseDisjoint_piece {g : α → ℝ} {R ε : ℝ} (hε : 0 < ε) (K : Set α) (J : Set ℕ) :
    J.PairwiseDisjoint (piece g R ε K) := fun _ _ _ _ hkl =>
  disjoint_left.2 fun _ hk hl => hkl ((eq_floor_of_mem_piece hε hk).trans
    (eq_floor_of_mem_piece hε hl).symm)

omit [MeasurableSpace α] in
theorem abs_sub_le_of_mem_piece {g : α → ℝ} {R ε : ℝ} {K : Set α} {k : ℕ} {x : α}
    (hx : x ∈ piece g R ε K k) : |g x - (-R + k * ε)| ≤ ε := by
  obtain ⟨-, h1, h2⟩ := hx
  rw [abs_le]; constructor <;> linarith

/-- **Densities from local Riemann–Stieltjes estimates.**  Let `s, t` be finite signed
measures, `g` bounded measurable, `D` measurable, and `B` a set function additive on disjoint
measurable subsets of `D`, such that `|t(A) − a s(A)| ≤ ε B(A)` for every measurable `A ⊆ D`
on which `|g − a| ≤ ε`.  Then `t(K) = ∫_K g ds` for every measurable `K ⊆ D`. -/
theorem eq_setIntegral_of_estimate (s t : SignedMeasure α) {g : α → ℝ} (hg : Measurable g)
    {R : ℝ} (hR : ∀ x, |g x| ≤ R) {D : Set α} (B : Set α → ℝ)
    (hB : ∀ A A', MeasurableSet A → MeasurableSet A' → A ⊆ D → A' ⊆ D → Disjoint A A' →
      B (A ∪ A') = B A + B A')
    (hest : ∀ A, MeasurableSet A → A ⊆ D → ∀ a ε, 0 < ε → (∀ x ∈ A, |g x - a| ≤ ε) →
      |t A - a * s A| ≤ ε * B A)
    {K : Set α} (hK : MeasurableSet K) (hKD : K ⊆ D) :
    t K = ∫ᵛ x in K, g x ∂<•s := by
  refine sub_eq_zero.1 (eq_zero_of_forall_abs_le (c := B K + s.variation.real K) fun ε hε => ?_)
  set J := Finset.range (⌈2 * R / ε⌉₊ + 1)
  have hP : ∀ k ∈ J, MeasurableSet (piece g R ε K k) := fun k _ =>
    hK.inter (hg measurableSet_Ico)
  have hPD : ∀ k ∈ J, piece g R ε K k ⊆ D := fun k _ => inter_subset_left.trans hKD
  have hd := pairwiseDisjoint_piece (g := g) (R := R) hε K (J : Set ℕ)
  have hU := biUnion_piece hε hR K
  have et : t K = ∑ k ∈ J, t (piece g R ε K k) := by
    conv_lhs => rw [← hU]
    exact sum_eq_of_additive (D := D) t (fun A A' hA hA' _ _ h => t.of_union h hA hA') J _ hP
      hPD hd
  have eI : ∫ᵛ x in K, g x ∂<•s = ∑ k ∈ J, ∫ᵛ x in piece g R ε K k, g x ∂<•s := by
    conv_lhs => rw [← hU]
    exact sum_eq_of_additive (D := D) (fun A => ∫ᵛ x in A, g x ∂<•s)
      (fun A A' hA hA' _ _ h => setIntegral_union h hA hA' (integrableOn_of_bound s hg hR A)
        (integrableOn_of_bound s hg hR A')) J _ hP hPD hd
  have eB : B K + s.variation.real K =
      ∑ k ∈ J, (B (piece g R ε K k) + s.variation.real (piece g R ε K k)) := by
    conv_lhs => rw [← hU]
    exact sum_eq_of_additive (D := D) (fun A => B A + s.variation.real A)
      (fun A A' hA hA' hAD hA'D h => by
        rw [hB A A' hA hA' hAD hA'D h, measureReal_union h hA']
        ring) J _ hP hPD hd
  rw [et, eI, eB, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  have hx : ∀ x ∈ piece g R ε K k, |g x - (-R + k * ε)| ≤ ε := fun x hx =>
    abs_sub_le_of_mem_piece hx
  have h1 := hest _ (hP k hk) (hPD k hk) _ ε hε hx
  have h2 := abs_setIntegral_sub_le s hg hR hx
  calc |t (piece g R ε K k) - ∫ᵛ x in piece g R ε K k, g x ∂<•s|
      ≤ |t (piece g R ε K k) - (-R + k * ε) * s (piece g R ε K k)| +
        |∫ᵛ x in piece g R ε K k, g x ∂<•s - (-R + k * ε) * s (piece g R ε K k)| :=
        by have := abs_sub_le (t (piece g R ε K k)) ((-R + k * ε) * s (piece g R ε K k))
             (∫ᵛ x in piece g R ε K k, g x ∂<•s)
           rwa [abs_sub_comm ((-R + k * ε) * s (piece g R ε K k))] at this
    _ ≤ ε * B (piece g R ε K k) + ε * s.variation.real (piece g R ε K k) := add_le_add h1 h2
    _ = _ := by ring

/-- Two set functions additive on disjoint measurable sets that agree on the measurable subsets
of each `D j`, `j ∈ J` (a finite family), agree on the measurable subsets of `⋃_{j ∈ J} D j`. -/
theorem eq_of_finset_cover (t u : Set α → ℝ)
    (ht : ∀ A A', MeasurableSet A → MeasurableSet A' → Disjoint A A' → t (A ∪ A') = t A + t A')
    (hu : ∀ A A', MeasurableSet A → MeasurableSet A' → Disjoint A A' → u (A ∪ A') = u A + u A')
    {ι : Type*} (D : ι → Set α) (hD : ∀ j, MeasurableSet (D j))
    (hloc : ∀ j, ∀ K, MeasurableSet K → K ⊆ D j → t K = u K) (J : Finset ι) :
    ∀ K, MeasurableSet K → K ⊆ ⋃ j ∈ J, D j → t K = u K := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    intro K _ hKJ
    have hK0 : K = ∅ := by simpa using hKJ
    subst hK0
    have h1 := ht ∅ ∅ MeasurableSet.empty MeasurableSet.empty (disjoint_empty _)
    have h2 := hu ∅ ∅ MeasurableSet.empty MeasurableSet.empty (disjoint_empty _)
    rw [union_empty] at h1 h2
    linarith
  | insert j J _ IH =>
    intro K hK hKJ
    have e : K = (K ∩ D j) ∪ (K \ D j) := (inter_union_sdiff K (D j)).symm
    have hdisj : Disjoint (K ∩ D j) (K \ D j) := disjoint_sdiff_inter.symm.mono_left
      (by rw [inter_comm])
    rw [e, ht _ _ (hK.inter (hD j)) (hK.diff (hD j)) hdisj,
      hu _ _ (hK.inter (hD j)) (hK.diff (hD j)) hdisj,
      hloc j _ (hK.inter (hD j)) inter_subset_right]
    congr 1
    refine IH _ (hK.diff (hD j)) fun x hx => ?_
    have := hKJ hx.1
    simp only [Finset.set_biUnion_insert, mem_union] at this
    exact this.resolve_left hx.2

/-- **Densities from local estimates on a compact space.**  If every point has an open
neighbourhood `D` and a set function `B`, additive on disjoint measurable subsets of `D`, with
`|t(A) − a s(A)| ≤ ε B(A)` for every measurable `A ⊆ D` on which `|g − a| ≤ ε`, then
`t(K) = ∫_K g ds` for every measurable `K`: the signed measure `t` has density `g` with respect
to `s`. -/
theorem eq_setIntegral_of_local_estimate [TopologicalSpace α] [CompactSpace α]
    (hopen : ∀ U : Set α, IsOpen U → MeasurableSet U) (s t : SignedMeasure α) {g : α → ℝ}
    (hg : Measurable g) {R : ℝ} (hR : ∀ x, |g x| ≤ R)
    (hloc : ∀ q : α, ∃ D : Set α, IsOpen D ∧ q ∈ D ∧ ∃ B : Set α → ℝ,
      (∀ A A', MeasurableSet A → MeasurableSet A' → A ⊆ D → A' ⊆ D → Disjoint A A' →
        B (A ∪ A') = B A + B A') ∧
      ∀ A, MeasurableSet A → A ⊆ D → ∀ a ε, 0 < ε → (∀ x ∈ A, |g x - a| ≤ ε) →
        |t A - a * s A| ≤ ε * B A)
    {K : Set α} (hK : MeasurableSet K) : t K = ∫ᵛ x in K, g x ∂<•s := by
  choose D hDo hqD B hB hest using hloc
  obtain ⟨J, hJ⟩ := isCompact_univ.elim_finite_subcover D hDo
    fun q _ => mem_iUnion.2 ⟨q, hqD q⟩
  exact eq_of_finset_cover (fun A => t A) (fun A => ∫ᵛ x in A, g x ∂<•s)
    (fun A A' hA hA' h => t.of_union h hA hA')
    (fun A A' hA hA' h => setIntegral_union h hA hA' (integrableOn_of_bound s hg hR A)
      (integrableOn_of_bound s hg hR A'))
    D (fun j => hopen _ (hDo j))
    (fun j K hK hKD => eq_setIntegral_of_estimate s t hg hR (B j) (hB j) (hest j) hK hKD) J K hK
    (fun x _ => hJ (mem_univ x))

end SignedDensity

end Polyfold
