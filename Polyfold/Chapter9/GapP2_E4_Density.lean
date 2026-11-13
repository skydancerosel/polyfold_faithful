import Polyfold.Chapter9.GapP2_E4_DensitySigned
import Polyfold.Chapter9.GapP2_E3_Density

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5 "Integration and Stokes": **(9.22)**, p. 441 (gap G.107).

# (9.22): `dμ_τ = f̄ · dμ_ω` for `τ = f · ω`, as an identity of signed measures

## The text, paraphrased

(p. 441) If `τ = f · ω`, then `dμ_τ = f̄ dμ_ω` for the measures of (9.21) on `|U(x)|`, with
`f̄ ∘ π = f`; the fact is used later (for the measures of Theorems 9.5.4 and 9.5.5).

## What is formalized

For the concrete integration `F.sheetIntegration` of `GapP2_E3_SheetIntegration.lean`, the
measures `μ_ω = branchedMeasure …` of Theorem 9.5.4 and `branchedMeasureEff …` of Theorem 9.5.5
(E1), `τ = f · ω` read as `F.IsMul τ ω f` (E3), and `f̄ : S → ℝ` bounded and `L(S)`-measurable with
`f = f̄ ∘ π` (e.g. `f̄` continuous on the compact `S`):

* **`branchedMeasure_eq_setIntegral_mul`** (**(9.22)**): `μ_τ(K) = ∫_K f̄ dμ_ω` for every
  `K ∈ L(S)`, the integral against the signed measure `μ_ω` being Mathlib's
  `∫ᵛ q in K, f̄ q ∂<•μ_ω`, which is `∫_K f̄ dμ_ω⁺ − ∫_K f̄ dμ_ω⁻` for the Jordan decomposition
  (`branchedMeasure_eq_jordan`);
* **`branchedMeasureEff_eq_setIntegral_mul`**: the same for the effective measure;
* `…_of_continuous`: the same for continuous `f̄` (bounded and measurable automatically).

The proof (`eq_setIntegral_of_sheetSum`): near each point of `S` a structure with sheets in the
class gives E3's estimate `|μ_τ(A) − a μ_ω(A)| ≤ ε · c ∑ σᵢ ∫_{Aᵢ} |ω|` for `A ⊆ |U(x)|` on which
`|f̄ − a| ≤ ε`; the right side is additive in `A` (`absSheetSum_union`), so
`SignedDensity.eq_setIntegral_of_local_estimate` (finite subcover of the compact `S`,
Riemann–Stieltjes sums, `ε → 0`) applies.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory VectorMeasure ContinuousLinearMap

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {n : ℕ} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω] {F : X.FormEval n Ω}

namespace FormEval

variable {N : Set Obj}

theorem absInteg_empty (hN : N ∈ F.sheets) (ω : Ω) : F.absInteg hN ω ∅ = 0 := by
  unfold absInteg
  rw [empty_inter, image_empty, Measure.restrict_empty, integral_zero_measure]

/-- `∫_A |ω|` is additive in `A`. -/
theorem absInteg_union (hN : N ∈ F.sheets) (ω : Ω) {A A' : Set Obj}
    (hA' : F.sheetNull.IsMeasIn N A') (hd : Disjoint A A') :
    F.absInteg hN ω (A ∪ A') = F.absInteg hN ω A + F.absInteg hN ω A' := by
  unfold absInteg
  have hint : IntegrableOn (fun u => |F.ev ω ((chart hN).tvec ((chart hN).q u))|)
      (chart hN).dom volume := (integrableOn_chart hN ω).abs
  have hdisj : Disjoint ((chart hN).coord '' (A ∩ N)) ((chart hN).coord '' (A' ∩ N)) := by
    refine disjoint_left.2 ?_
    rintro _ ⟨y, hy, rfl⟩ ⟨y', hy', he⟩
    have e : y' = y := (chart hN).injOn_coord hy'.2 hy.2 he
    exact disjoint_left.1 hd hy.1 (e ▸ hy'.1)
  rw [union_inter_distrib_right, image_union]
  exact setIntegral_union₀ hdisj.aedisjoint (nullMeasurableSet_coord_image _ hA')
    (IntegrableOn.mono_set hint (image_mono inter_subset_right))
    (IntegrableOn.mono_set hint (image_mono inter_subset_right))

end FormEval

namespace OrientedTameStructure

variable {Θ : Obj → ℚ} {x : Obj} (C : X.OrientedTameStructure n Θ x)

/-- `∑ σᵢ ∫_{A ∩ Mᵢ} |ω|` is additive in `A`. -/
theorem absSheetSum_union (hS : ∀ i, C.M i ∈ F.sheets) (ω : Ω) {A A' : Set Obj}
    (hA' : C.IsMeas F.sheetNull A') (hd : Disjoint A A') :
    C.absSheetSum F hS ω (A ∪ A') = C.absSheetSum F hS ω A + C.absSheetSum F hS ω A' := by
  unfold absSheetSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [union_inter_distrib_right, FormEval.absInteg_union (hS i) ω
    ((hA' i).inter (SheetNullSets.isMeasIn_self _))
    (hd.mono inter_subset_left inter_subset_left), mul_add]

end OrientedTameStructure

section Global

variable {Θ : Obj → ℚ}

open OrientedTameStructure

/-- **Densities of the measures of §9.5 from (9.21).**  Let `Φ : Ω → signed measures on
`(S, L(S))` be given, for a class `Good` of oriented tame structures with sheets in `F.sheets`
(one at every point of `supp Θ`), by `Φ_ω(K) = c(x) ∑ σᵢ ∫_{Kᵢ} ω|(Mᵢ, oᵢ)` for `K ⊆ |U(x)|`,
with `c ≥ 0`.  If `τ = f · ω` and `f = f̄ ∘ π` with `f̄` bounded and `L(S)`-measurable, then
`Φ_τ(K) = ∫_K f̄ dΦ_ω` for every `K ∈ L(S)`. -/
theorem eq_setIntegral_of_sheetSum (hn : 0 < n) (hcpt : X.IsCompactBranched Θ)
    (Good : ∀ x, X.OrientedTameStructure n Θ x → Prop)
    (hGS : ∀ x C, Good x C → ∀ i, C.M i ∈ F.sheets)
    (hcov : ∀ x ∈ supp Θ, ∃ C, Good x C) (c : Obj → ℝ) (hc : ∀ x, 0 ≤ c x)
    (Φ : Ω → @SignedMeasure (X.orbitSupp Θ) (X.lebesgueSigma F.sheetNull Θ))
    (hΦ : ∀ ω x (C : X.OrientedTameStructure n Θ x), Good x C → ∀ K : Set (X.orbitSupp Θ),
      MeasurableSet[X.lebesgueSigma F.sheetNull Θ] K → Subtype.val '' K ⊆ X.π '' C.U →
      Φ ω K = c x * C.sheetSum (F.sheetIntegration hn) ω (X.π ⁻¹' (Subtype.val '' K)))
    {τ ω : Ω} {f : Obj → ℝ} (h : F.IsMul τ ω f) (fbar : X.orbitSupp Θ → ℝ)
    (hfm : Measurable[X.lebesgueSigma F.sheetNull Θ] fbar) {R : ℝ} (hR : ∀ q, |fbar q| ≤ R)
    (hf : ∀ (q : X.orbitSupp Θ) (y : Obj), X.π y = q.1 → f y = fbar q)
    {K : Set (X.orbitSupp Θ)} (hK : MeasurableSet[X.lebesgueSigma F.sheetNull Θ] K) :
    Φ τ K = ∫ᵛ q in K, fbar q ∂<•(Φ ω) := by
  let _ : MeasurableSpace (X.orbitSupp Θ) := X.lebesgueSigma F.sheetNull Θ
  have : CompactSpace (X.orbitSupp Θ) := isCompact_iff_compactSpace.1 hcpt
  have hTS : X.HasTameSheetsIn F.sheets Θ := fun x hx => by
    obtain ⟨C, hC⟩ := hcov x hx
    exact ⟨C.toTameBranchingStructure, hGS x C hC⟩
  refine SignedDensity.eq_setIntegral_of_local_estimate
    (fun U hU => borel_le_borelNullSigma _ _ (MeasurableSpace.measurableSet_generateFrom hU))
    (Φ ω) (Φ τ) hfm hR (fun q => ?_) hK
  obtain ⟨y, hy, hyq⟩ := q.2
  obtain ⟨C, hC⟩ := hcov y hy
  have hS := hGS y C hC
  have hsub : ∀ {A : Set (X.orbitSupp Θ)}, A ⊆ Subtype.val ⁻¹' (X.π '' C.U) →
      Subtype.val '' A ⊆ X.π '' C.U := by
    rintro A hA _ ⟨q, hq, rfl⟩
    exact hA hq
  refine ⟨Subtype.val ⁻¹' (X.π '' C.U),
    (X.proposition_7_1_8 _ C.isOpen_U).preimage continuous_subtype_val, ⟨y, C.mem_U, hyq⟩,
    fun A => c y * C.absSheetSum F hS ω (X.π ⁻¹' (Subtype.val '' A)), ?_, ?_⟩
  · intro A A' hA hA' _ _ hd
    have hd' : Disjoint (X.π ⁻¹' (Subtype.val '' A)) (X.π ⁻¹' (Subtype.val '' A')) :=
      ((Set.disjoint_image_iff Subtype.val_injective).2 hd).preimage _
    dsimp only
    rw [image_union, preimage_union, C.absSheetSum_union hS ω (C.isMeas_preimage hTS hS hA') hd', mul_add]
  · intro A hA hAD a ε _ hx
    rw [hΦ τ y C hC A hA (hsub hAD), hΦ ω y C hC A hA (hsub hAD)]
    have h1 := C.abs_sheetSum_sub_le hn hS h (C.isMeas_preimage hTS hS hA) (a := a) (ε := ε)
      fun y' hy' => by
        obtain ⟨q', hq', he⟩ := hy'
        rw [hf q' y' he.symm]
        exact hx q' hq'
    calc |c y * C.sheetSum (F.sheetIntegration hn) τ (X.π ⁻¹' (Subtype.val '' A)) -
          a * (c y * C.sheetSum (F.sheetIntegration hn) ω (X.π ⁻¹' (Subtype.val '' A)))|
        = c y * |C.sheetSum (F.sheetIntegration hn) τ (X.π ⁻¹' (Subtype.val '' A)) -
          a * C.sheetSum (F.sheetIntegration hn) ω (X.π ⁻¹' (Subtype.val '' A))| := by
          rw [← mul_left_comm, ← mul_sub, abs_mul, abs_of_nonneg (hc y)]
      _ ≤ c y * (ε * C.absSheetSum F hS ω (X.π ⁻¹' (Subtype.val '' A))) :=
          mul_le_mul_of_nonneg_left h1 (hc y)
      _ = ε * (c y * C.absSheetSum F hS ω (X.π ⁻¹' (Subtype.val '' A))) := by ring

/-- **(9.22), 2021 p. 441, for the measure of
Theorem 9.5.4**: if `τ = f · ω` and `f = f̄ ∘ π` with `f̄ : S → ℝ` bounded and `L(S)`-measurable,
then `μ_τ(K) = ∫_K f̄ dμ_ω` for every `K ∈ L(S)`, i.e. `dμ_τ = f̄ dμ_ω`.  The text states it for
the local measures on `|U(x)|`; this is the global form used later. -/
theorem branchedMeasure_eq_setIntegral_mul (hn : 0 < n) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ F.sheets) ∧ C.Represents T)
    {τ ω : Ω} {f : Obj → ℝ} (h : F.IsMul τ ω f) (fbar : X.orbitSupp Θ → ℝ)
    (hfm : Measurable[X.lebesgueSigma F.sheetNull Θ] fbar) {R : ℝ} (hR : ∀ q, |fbar q| ≤ R)
    (hf : ∀ (q : X.orbitSupp Θ) (y : Obj), X.π y = q.1 → f y = fbar q)
    {K : Set (X.orbitSupp Θ)} (hK : MeasurableSet[X.lebesgueSigma F.sheetNull Θ] K) :
    branchedMeasure (F.sheetIntegration hn) hΘ hcpt hT hcov τ K =
      ∫ᵛ q in K, fbar q ∂<•(branchedMeasure (F.sheetIntegration hn) hΘ hcpt hT hcov ω) :=
  eq_setIntegral_of_sheetSum hn hcpt (fun _ C => (∀ i, C.M i ∈ F.sheets) ∧ C.Represents T)
    (fun _ _ hC => hC.1) hcov (fun x => (Nat.card (X.Isotropy x) : ℝ)⁻¹)
    (fun _ => inv_nonneg.2 (Nat.cast_nonneg _))
    (fun ω => branchedMeasure (F.sheetIntegration hn) hΘ hcpt hT hcov ω)
    (fun ω _ C hC _ hK hKU =>
      branchedMeasure_apply (F.sheetIntegration hn) hΘ hcpt hT hcov ω C hC.1 hC.2 hK hKU)
    h fbar hfm hR hf hK

/-- **(9.22), 2021 p. 441, for the measure of Theorem 9.5.5** (the effective measure):
`μ_τ^eff(K) = ∫_K f̄ dμ_ω^eff` for every `K ∈ L(S)`. -/
theorem branchedMeasureEff_eq_setIntegral_mul (hn : 0 < n) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ F.sheets) ∧ C.Represents T ∧ C.rep.HasLUC)
    {τ ω : Ω} {f : Obj → ℝ} (h : F.IsMul τ ω f) (fbar : X.orbitSupp Θ → ℝ)
    (hfm : Measurable[X.lebesgueSigma F.sheetNull Θ] fbar) {R : ℝ} (hR : ∀ q, |fbar q| ≤ R)
    (hf : ∀ (q : X.orbitSupp Θ) (y : Obj), X.π y = q.1 → f y = fbar q)
    {K : Set (X.orbitSupp Θ)} (hK : MeasurableSet[X.lebesgueSigma F.sheetNull Θ] K) :
    branchedMeasureEff (F.sheetIntegration hn) hΘ hcpt hT hcov τ K =
      ∫ᵛ q in K, fbar q ∂<•(branchedMeasureEff (F.sheetIntegration hn) hΘ hcpt hT hcov ω) :=
  eq_setIntegral_of_sheetSum hn hcpt
    (fun _ C => (∀ i, C.M i ∈ F.sheets) ∧ C.Represents T ∧ C.rep.HasLUC)
    (fun _ _ hC => hC.1) hcov (fun x => (Nat.card (X.EffIsotropy x) : ℝ)⁻¹)
    (fun _ => inv_nonneg.2 (Nat.cast_nonneg _))
    (fun ω => branchedMeasureEff (F.sheetIntegration hn) hΘ hcpt hT hcov ω)
    (fun ω _ C hC _ hK hKU =>
      branchedMeasureEff_apply (F.sheetIntegration hn) hΘ hcpt hT hcov ω C hC.1 hC.2.1 hC.2.2
        hK hKU)
    h fbar hfm hR hf hK

/-- **(9.22) with the Jordan decomposition**: `μ_τ(K) = ∫_K f̄ dμ_ω⁺ − ∫_K f̄ dμ_ω⁻`. -/
theorem branchedMeasure_eq_jordan (hn : 0 < n) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ F.sheets) ∧ C.Represents T)
    {τ ω : Ω} {f : Obj → ℝ} (h : F.IsMul τ ω f) (fbar : X.orbitSupp Θ → ℝ)
    (hfm : Measurable[X.lebesgueSigma F.sheetNull Θ] fbar) {R : ℝ} (hR : ∀ q, |fbar q| ≤ R)
    (hf : ∀ (q : X.orbitSupp Θ) (y : Obj), X.π y = q.1 → f y = fbar q)
    {K : Set (X.orbitSupp Θ)} (hK : MeasurableSet[X.lebesgueSigma F.sheetNull Θ] K) :
    letI : MeasurableSpace (X.orbitSupp Θ) := X.lebesgueSigma F.sheetNull Θ
    branchedMeasure (F.sheetIntegration hn) hΘ hcpt hT hcov τ K =
      ∫ q in K, fbar q ∂(branchedMeasure (F.sheetIntegration hn) hΘ hcpt hT hcov
          ω).toJordanDecomposition.posPart -
        ∫ q in K, fbar q ∂(branchedMeasure (F.sheetIntegration hn) hΘ hcpt hT hcov
          ω).toJordanDecomposition.negPart := by
  let _ : MeasurableSpace (X.orbitSupp Θ) := X.lebesgueSigma F.sheetNull Θ
  rw [branchedMeasure_eq_setIntegral_mul hn hΘ hcpt hT hcov h fbar hfm hR hf hK]
  exact SignedDensity.setIntegral_eq_jordan _ hfm hR hK

/-- A continuous `f̄` on the compact `S` is bounded and `L(S)`-measurable. -/
theorem measurable_and_bounded_of_continuous (hcpt : X.IsCompactBranched Θ)
    {fbar : X.orbitSupp Θ → ℝ} (hc : Continuous fbar) :
    Measurable[X.lebesgueSigma F.sheetNull Θ] fbar ∧ ∃ R, ∀ q, |fbar q| ≤ R := by
  let _ : MeasurableSpace (X.orbitSupp Θ) := X.lebesgueSigma F.sheetNull Θ
  have : CompactSpace (X.orbitSupp Θ) := isCompact_iff_compactSpace.1 hcpt
  refine ⟨measurable_of_isOpen fun U hU =>
    borel_le_borelNullSigma _ _ (MeasurableSpace.measurableSet_generateFrom (hU.preimage hc)), ?_⟩
  obtain ⟨R, hR⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact ⟨R, fun q => by simpa [Real.norm_eq_abs] using hR q (mem_univ q)⟩

/-- **(9.22), 2021 p. 441, for continuous `f̄`** (the text's sc-smooth `f`): for the measure of
Theorem 9.5.4, `μ_τ(K) = ∫_K f̄ dμ_ω` for every `K ∈ L(S)`. -/
theorem branchedMeasure_eq_setIntegral_mul_of_continuous (hn : 0 < n)
    (hΘ : X.IsBranchedEpSubgroupoid Θ) (hcpt : X.IsCompactBranched Θ)
    {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ F.sheets) ∧ C.Represents T)
    {τ ω : Ω} {f : Obj → ℝ} (h : F.IsMul τ ω f) (fbar : X.orbitSupp Θ → ℝ)
    (hfc : Continuous fbar) (hf : ∀ (q : X.orbitSupp Θ) (y : Obj), X.π y = q.1 → f y = fbar q)
    {K : Set (X.orbitSupp Θ)} (hK : MeasurableSet[X.lebesgueSigma F.sheetNull Θ] K) :
    branchedMeasure (F.sheetIntegration hn) hΘ hcpt hT hcov τ K =
      ∫ᵛ q in K, fbar q ∂<•(branchedMeasure (F.sheetIntegration hn) hΘ hcpt hT hcov ω) := by
  obtain ⟨hfm, R, hR⟩ := measurable_and_bounded_of_continuous (F := F) hcpt hfc
  exact branchedMeasure_eq_setIntegral_mul hn hΘ hcpt hT hcov h fbar hfm hR hf hK

/-- **(9.22), 2021 p. 441, for continuous `f̄`, effective measure** (Theorem 9.5.5). -/
theorem branchedMeasureEff_eq_setIntegral_mul_of_continuous (hn : 0 < n)
    (hΘ : X.IsBranchedEpSubgroupoid Θ) (hcpt : X.IsCompactBranched Θ)
    {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ F.sheets) ∧ C.Represents T ∧ C.rep.HasLUC)
    {τ ω : Ω} {f : Obj → ℝ} (h : F.IsMul τ ω f) (fbar : X.orbitSupp Θ → ℝ)
    (hfc : Continuous fbar) (hf : ∀ (q : X.orbitSupp Θ) (y : Obj), X.π y = q.1 → f y = fbar q)
    {K : Set (X.orbitSupp Θ)} (hK : MeasurableSet[X.lebesgueSigma F.sheetNull Θ] K) :
    branchedMeasureEff (F.sheetIntegration hn) hΘ hcpt hT hcov τ K =
      ∫ᵛ q in K, fbar q ∂<•(branchedMeasureEff (F.sheetIntegration hn) hΘ hcpt hT hcov ω) := by
  obtain ⟨hfm, R, hR⟩ := measurable_and_bounded_of_continuous (F := F) hcpt hfc
  exact branchedMeasureEff_eq_setIntegral_mul hn hΘ hcpt hT hcov h fbar hfm hR hf hK

end Global

end EpGroupoid

end Polyfold
