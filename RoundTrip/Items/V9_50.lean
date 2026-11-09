import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_50

/-!
Round trip for V9_50 (Lemma 9.5.2, 2021 p. 437; 2017: Lemma 9.16, p. 322): measure zero in `S`
does not depend on the choice of the local branching structures.

`A` (universes at `0`) is the conjunction of the types of `isMeasureZeroSuppAll_of_any`,
`isMeasureZeroSuppAny_of_isMeasureZeroSupp`, `lemma_9_5_2`, `isSigmaIdeal_isMeasureZeroSupp`,
`isSigmaIdeal_isMeasureZeroSuppAll`, `not_isMeasureZeroSuppAny_orbitSupp`,
`not_isMeasureZeroSupp_orbitSupp` and `isNull_transfer_mixed_dim` (no universe).  All of them are
about an **abstract** null-set system `G : SheetNullSets S` on a class `S` of sheets, whose field
`isNull_transfer` (two sheets of `S` induce the same null sets on their intersection) carries the
content of the lemma; `B` uses a **concrete** notion, `IsLocNullB` (locally `n`-dimensional
Hausdorff-null in every chart of the object M-polyfold), which is a property of the set alone.

* `A ⇒ B` holds **outright** (`B_holds`, hypothesis not used): because `IsLocNullB` does not
  depend on the sheet, the covering argument needs no transfer property.  At `z ∈ M'ⱼ ∩ π⁻¹(K)`
  take the structure `(Mᵢ)` on `U(z)` given by the hypothesis; on `U(z)` the support is `⋃ Mᵢ`;
  for `z ∈ Mᵢ` use the open set of `IsLocNullB (Mᵢ ∩ π⁻¹K)` at `z`, for `z ∉ Mᵢ` the open set
  `U(z) ∖ Mᵢ` (open since `Mᵢ → U(z)` is proper, `isOpen_U_diff_M`); a finite union of null sets
  is null.  Neither tameness, nor dimension, nor suitability of the structures is used.
* `A ⇒ B` through `A` (`A_to_B_of_hyp`): `A`'s `isMeasureZeroSuppAll_of_any` applies to B's
  notion through the `SheetNullSets` `hausdorffNull` on the class `GoodSheets` of sheets on which
  `IsLocNullB` is closed under countable unions of subsets and which are not null in themselves.
  All fields are then immediate (transfer is trivial, the notion being sheet-independent).  The
  extra hypothesis is that the sheets of suitable structures are good; this is not proved: it
  needs local second countability of the sheets (in a non-separable `E₀` locally null sets are
  not closed under countable unions in general) and positivity of the `n`-dimensional Hausdorff
  measure of an `n`-dimensional sheet in a chart (and fails for a sheet of dimension `< n`).
* `B ⇒ A` (`B_to_A`) is **vacuous**: `B` says nothing about abstract `SheetNullSets`; `A` is
  re-proved outright (copies of the project's short proofs, section `ReProof`).
-/

namespace RoundTrip.V9_50
open Polyfold Set MeasureTheory

/-- The project's statements, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.EpGroupoid.isMeasureZeroSuppAll_of_any.{0} ∧
  type_of% @Polyfold.EpGroupoid.isMeasureZeroSuppAny_of_isMeasureZeroSupp.{0} ∧
  type_of% @Polyfold.EpGroupoid.lemma_9_5_2.{0} ∧
  type_of% @Polyfold.EpGroupoid.isSigmaIdeal_isMeasureZeroSupp.{0} ∧
  type_of% @Polyfold.EpGroupoid.isSigmaIdeal_isMeasureZeroSuppAll.{0} ∧
  type_of% @Polyfold.EpGroupoid.not_isMeasureZeroSuppAny_orbitSupp.{0} ∧
  type_of% @Polyfold.EpGroupoid.not_isMeasureZeroSupp_orbitSupp.{0} ∧
  type_of% @Polyfold.isNull_transfer_mixed_dim

theorem A_holds : A :=
  ⟨@EpGroupoid.isMeasureZeroSuppAll_of_any, @EpGroupoid.isMeasureZeroSuppAny_of_isMeasureZeroSupp,
    @EpGroupoid.lemma_9_5_2, @EpGroupoid.isSigmaIdeal_isMeasureZeroSupp,
    @EpGroupoid.isSigmaIdeal_isMeasureZeroSuppAll, @EpGroupoid.not_isMeasureZeroSuppAny_orbitSupp,
    @EpGroupoid.not_isMeasureZeroSupp_orbitSupp, @isNull_transfer_mixed_dim⟩

/-! ### `B` holds outright -/

/-- **Lemma 9.5.2 for B's notion, outright**: the covering argument. -/
theorem B_holds : B := by
  intro Obj Mor _ _ _ _ _ _ X Θ n _ _ _ K _ hK x' _ B' _ j z hz
  have hzs : z ∈ EpGroupoid.supp Θ := (B'.mem_supp_iff (B'.subset_U j hz.1)).2 ⟨j, hz.1⟩
  obtain ⟨Bz, -, hBnull⟩ := hK z hzs
  have hV : ∀ i, ∃ V : Set Obj, IsOpen V ∧ z ∈ V ∧ ∀ φ : MChart Obj, X.PObj.IsChart φ →
      OuterMeasure.mkMetric (fun r : ENNReal => r ^ (n : ℝ))
        (φ.toPartialEquiv '' (Bz.M i ∩ X.π ⁻¹' K ∩ V ∩ φ.toPartialEquiv.source)) = 0 := by
    intro i
    by_cases hzi : z ∈ Bz.M i
    · exact hBnull i z ⟨hzi, hz.2⟩
    · refine ⟨Bz.U \ Bz.M i, Bz.isOpen_U_diff_M i, ⟨Bz.mem_U, hzi⟩, fun φ _ => ?_⟩
      have h0 : Bz.M i ∩ X.π ⁻¹' K ∩ (Bz.U \ Bz.M i) ∩ φ.toPartialEquiv.source = ∅ := by
        ext w
        simp only [mem_inter_iff, mem_sdiff, mem_empty_iff_false, iff_false]
        tauto
      rw [h0, image_empty, measure_empty]
  choose V hVo hzV hVnull using hV
  refine ⟨Bz.U ∩ ⋂ i, V i, Bz.isOpen_U.inter (isOpen_iInter_of_finite hVo),
    ⟨Bz.mem_U, mem_iInter.2 hzV⟩, fun φ hφ => ?_⟩
  refine measure_mono_null ?_ (measure_iUnion_null fun i => hVnull i φ hφ)
  rintro _ ⟨w, ⟨⟨⟨hwM, hwK⟩, hwU, hwV⟩, hws⟩, rfl⟩
  have hwS : w ∈ EpGroupoid.supp Θ := (B'.mem_supp_iff (B'.subset_U j hwM)).2 ⟨j, hwM⟩
  obtain ⟨i, hi⟩ := (Bz.mem_supp_iff hwU).1 hwS
  exact mem_iUnion.2 ⟨i, w, ⟨⟨⟨hi, hwK⟩, mem_iInter.1 hwV i⟩, hws⟩, rfl⟩

/-- `A ⇒ B` in the sense of the harness: `B` is proved outright (the hypothesis is not used). -/
theorem A_to_B : A → B := fun _ => B_holds

/-! ### `A ⇒ B` through `A`, for good sheets -/

section Good
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

theorem isLocNullB_mono {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    {P : MPolyfold Z} {d : ℕ} {C C' : Set Z} (h : IsLocNullB P d C') (hC : C ⊆ C') :
    IsLocNullB P d C := by
  intro z hz
  obtain ⟨V, hV, hzV, hnull⟩ := h z (hC hz)
  exact ⟨V, hV, hzV, fun φ hφ => measure_mono_null
    (image_mono (inter_subset_inter_left _ (inter_subset_inter_left _ hC))) (hnull φ hφ)⟩

/-- The sheets on which B's null sets behave as a `SheetNullSets` asks: locally null subsets are
closed under countable unions, and the sheet is not null in itself. -/
def GoodSheets (X : EpGroupoid Obj Mor) (n : ℕ) : Set (Set Obj) :=
  {N | (∀ C : ℕ → Set Obj, (∀ k, IsLocNullB X.PObj n (C k ∩ N)) →
      IsLocNullB X.PObj n ((⋃ k, C k) ∩ N)) ∧ (N.Nonempty → ¬ IsLocNullB X.PObj n N)}

/-- B's null sets as a `SheetNullSets` on the good sheets. -/
def hausdorffNull (X : EpGroupoid Obj Mor) (n : ℕ) : SheetNullSets (GoodSheets X n) where
  IsNull N C := N ∈ GoodSheets X n → IsLocNullB X.PObj n (C ∩ N)
  isNull_empty N _ := fun z hz => (notMem_empty z hz.1).elim
  isNull_mono h hC hN := isLocNullB_mono (h hN) (inter_subset_inter_left _ hC)
  isNull_iUnion h hN := hN.1 _ fun k => h k hN
  isNull_of_local N hN C h _ := by
    intro z hz
    obtain ⟨V, hVo, hzV, hV⟩ := h z hz.1
    obtain ⟨V', hV'o, hzV', hV'⟩ := hV hN z ⟨⟨hz.1, hzV⟩, hz.2⟩
    refine ⟨V ∩ V', hVo.inter hV'o, ⟨hzV, hzV'⟩, fun φ hφ => measure_mono_null
      (image_mono ?_) (hV' φ hφ)⟩
    rintro w ⟨⟨⟨hwC, hwN⟩, hwV, hwV'⟩, hws⟩
    exact ⟨⟨⟨⟨hwC, hwV⟩, hwN⟩, hwV'⟩, hws⟩
  isNull_transfer N hN N' _ C hC h _ := by
    have h1 : C ∩ N' = C := inter_eq_left.2 fun w hw => (hC hw).2
    have h2 : C ∩ N = C := inter_eq_left.2 fun w hw => (hC hw).1
    have h3 := h hN
    rw [h2] at h3
    rw [h1]
    exact h3
  not_isNull_self N hN hne h := hN.2 hne (isLocNullB_mono (h hN) fun w hw => ⟨hw, hw⟩)

end Good

/-- **`A ⇒ B` through `A`** (`isMeasureZeroSuppAll_of_any` for `hausdorffNull`), given that the
sheets of all suitable structures are good. -/
theorem A_to_B_of_hyp (hA : A)
    (hgood : ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
      (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) (n : ℕ),
      X.IsBranchedEpSubgroupoid Θ → IsTameB X Θ → X.IsNDimensional Θ n →
      ∀ x ∈ EpGroupoid.supp Θ, ∀ B : X.LocalBranchingStructure Θ x, IsSuitableB X B →
        ∀ i, B.M i ∈ GoodSheets X n) : B := by
  intro Obj Mor _ _ _ _ _ _ X Θ n hΘ hT hD K _ hK x' hx' B' hB' j
  have hg := hgood Obj Mor X Θ n hΘ hT hD
  have hany : X.IsMeasureZeroSuppAny (hausdorffNull X n) Θ K := fun x hx => by
    obtain ⟨Bx, hBx, hnull⟩ := hK x hx
    exact ⟨Bx, hg x hx Bx hBx, fun i _ => isLocNullB_mono (hnull i) inter_subset_left⟩
  have hall := hA.1 (hausdorffNull X n) hany
  exact isLocNullB_mono (hall x' hx' B' (hg x' hx' B' hB') j (hg x' hx' B' hB' j))
    fun w hw => ⟨hw, hw.1⟩

/-! ### `B ⇒ A`, vacuous: `A` re-proved outright -/

namespace ReProof
open EpGroupoid

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {S : Set (Set Obj)} (G : SheetNullSets S) {Θ : Obj → ℚ}

theorem all_of_any {A : Set X.OrbitSpace} (h : X.IsMeasureZeroSuppAny G Θ A) :
    X.IsMeasureZeroSuppAll G Θ A := by
  intro x' _ B' hB'S j
  refine G.isNull_of_cover (hB'S j) inter_subset_left fun z hz => ?_
  have hsupp : ∀ {w}, w ∈ B'.M j → w ∈ supp Θ := fun hw =>
    (B'.mem_supp_iff (B'.subset_U j hw)).2 ⟨j, hw⟩
  obtain ⟨B, hBS, hBnull⟩ := h z (hsupp hz.1)
  refine ⟨B.U, B.isOpen_U, B.mem_U, B.ι, inferInstance, B.M, hBS, fun w hw => ?_,
    fun i => G.isNull_mono (hBnull i) fun w hw => ⟨hw.2, hw.1.2⟩⟩
  exact mem_iUnion.2 ((B.mem_supp_iff hw.2).1 (hsupp hw.1.1))

theorem any_of_supp {A : Set X.OrbitSpace} (h : X.IsMeasureZeroSupp G Θ A) :
    X.IsMeasureZeroSuppAny G Θ A := fun x hx => by
  obtain ⟨B, hB⟩ := h x hx
  exact ⟨B.toLocalBranchingStructure, hB⟩

theorem lemma_re (hS : X.HasTameSheetsIn S Θ) (A : Set X.OrbitSpace) :
    (X.IsMeasureZeroSupp G Θ A ↔ X.IsMeasureZeroSuppAny G Θ A) ∧
      (X.IsMeasureZeroSuppAny G Θ A ↔ X.IsMeasureZeroSuppAll G Θ A) := by
  have hAll : X.IsMeasureZeroSuppAll G Θ A → X.IsMeasureZeroSupp G Θ A := fun h x hx => by
    obtain ⟨B, hBS⟩ := hS x hx
    exact ⟨B, hBS, h x hx _ hBS⟩
  exact ⟨⟨any_of_supp G, fun h => hAll (all_of_any G h)⟩,
    ⟨all_of_any G, fun h => any_of_supp G (hAll h)⟩⟩

theorem sigma_all : IsSigmaIdeal {A : Set X.OrbitSpace | X.IsMeasureZeroSuppAll G Θ A} where
  empty_mem _ _ B _ i := by
    rw [preimage_empty, inter_empty]
    exact G.isNull_empty _
  mono hB hAB x hx B' hS i :=
    G.isNull_mono (hB x hx B' hS i) (inter_subset_inter_right _ (preimage_mono hAB))
  iUnion_mem A hA x hx B hS i := by
    rw [preimage_iUnion, inter_iUnion]
    exact G.isNull_iUnion fun k => hA k x hx B hS i

theorem sigma_supp (hS : X.HasTameSheetsIn S Θ) :
    IsSigmaIdeal {A : Set X.OrbitSpace | X.IsMeasureZeroSupp G Θ A} := by
  have he : ∀ A, X.IsMeasureZeroSupp G Θ A ↔ X.IsMeasureZeroSuppAll G Θ A := fun A =>
    ((lemma_re G hS A).1).trans (lemma_re G hS A).2
  have h := sigma_all G (X := X) (Θ := Θ)
  exact ⟨(he ∅).2 h.empty_mem, fun hB hAB => (he _).2 (h.mono ((he _).1 hB) hAB),
    fun A hA => (he _).2 (h.iUnion_mem A fun k => (he _).1 (hA k))⟩

theorem not_any (hΘ : X.IsFunctorial Θ) (hne : (supp Θ).Nonempty) :
    ¬ X.IsMeasureZeroSuppAny G Θ (X.orbitSupp Θ) := by
  intro h
  obtain ⟨x, hx⟩ := hne
  obtain ⟨B, hBS, hBnull⟩ := h x hx
  obtain ⟨i, hi⟩ := (B.mem_supp_iff B.mem_U).1 hx
  have hsub : B.M i ⊆ B.M i ∩ X.π ⁻¹' X.orbitSupp Θ := fun w hw => ⟨hw, by
    rw [preimage_π_orbitSupp hΘ]
    exact (B.mem_supp_iff (B.subset_U i hw)).2 ⟨i, hw⟩⟩
  exact G.not_isNull_self _ (hBS i) ⟨x, hi⟩ (G.isNull_mono (hBnull i) hsub)

theorem not_supp (hΘ : X.IsFunctorial Θ) (hne : (supp Θ).Nonempty) :
    ¬ X.IsMeasureZeroSupp G Θ (X.orbitSupp Θ) := fun h =>
  not_any G hΘ hne (any_of_supp G h)

end

theorem mixed_dim_re : planeNull.IsNull univ axis2 ∧ ¬ graphNull.IsNull axis2 axis2 := by
  refine ⟨isMeasureZero_rn2_iff.2 ?_, graphNull.not_isNull_self axis2
    ⟨0, contDiff_const, univ, isOpen_univ, (inter_univ _).symm⟩ ⟨0, zero_mem_axis2⟩⟩
  refine measure_mono_null (fun v hv => ?_) (Measure.addHaar_submodule volume lineH lineH_ne_top)
  change v 1 = (0 : ℝ → ℝ) (v 0) at hv
  exact (mem_lineH).2 hv

end ReProof

/-- `B ⇒ A`, vacuous: `A` re-proved outright. -/
theorem B_to_A : B → A := fun _ =>
  ⟨@ReProof.all_of_any, @ReProof.any_of_supp, @ReProof.lemma_re, @ReProof.sigma_supp,
    @ReProof.sigma_all, @ReProof.not_any, @ReProof.not_supp, ReProof.mixed_dim_re⟩

#rt_check RoundTrip.V9_50.A_to_B [Polyfold.EpGroupoid.isMeasureZeroSuppAll_of_any,
  Polyfold.EpGroupoid.isMeasureZeroSuppAny_of_isMeasureZeroSupp, Polyfold.EpGroupoid.lemma_9_5_2,
  Polyfold.EpGroupoid.isSigmaIdeal_isMeasureZeroSupp,
  Polyfold.EpGroupoid.isSigmaIdeal_isMeasureZeroSuppAll,
  Polyfold.EpGroupoid.not_isMeasureZeroSuppAny_orbitSupp,
  Polyfold.EpGroupoid.not_isMeasureZeroSupp_orbitSupp, Polyfold.isNull_transfer_mixed_dim]
#rt_check RoundTrip.V9_50.A_to_B_of_hyp [Polyfold.EpGroupoid.isMeasureZeroSuppAll_of_any,
  Polyfold.EpGroupoid.isMeasureZeroSuppAny_of_isMeasureZeroSupp, Polyfold.EpGroupoid.lemma_9_5_2,
  Polyfold.EpGroupoid.isSigmaIdeal_isMeasureZeroSupp,
  Polyfold.EpGroupoid.isSigmaIdeal_isMeasureZeroSuppAll,
  Polyfold.EpGroupoid.not_isMeasureZeroSuppAny_orbitSupp,
  Polyfold.EpGroupoid.not_isMeasureZeroSupp_orbitSupp, Polyfold.isNull_transfer_mixed_dim]
#rt_check RoundTrip.V9_50.B_to_A [Polyfold.EpGroupoid.isMeasureZeroSuppAll_of_any,
  Polyfold.EpGroupoid.isMeasureZeroSuppAny_of_isMeasureZeroSupp, Polyfold.EpGroupoid.lemma_9_5_2,
  Polyfold.EpGroupoid.isSigmaIdeal_isMeasureZeroSupp,
  Polyfold.EpGroupoid.isSigmaIdeal_isMeasureZeroSuppAll,
  Polyfold.EpGroupoid.not_isMeasureZeroSuppAny_orbitSupp,
  Polyfold.EpGroupoid.not_isMeasureZeroSupp_orbitSupp, Polyfold.isNull_transfer_mixed_dim]
#rt_overlap RoundTrip.V9_50.B_to_A [Polyfold.EpGroupoid.isMeasureZeroSuppAll_of_any,
  Polyfold.EpGroupoid.isMeasureZeroSuppAny_of_isMeasureZeroSupp, Polyfold.EpGroupoid.lemma_9_5_2,
  Polyfold.EpGroupoid.isSigmaIdeal_isMeasureZeroSupp,
  Polyfold.EpGroupoid.isSigmaIdeal_isMeasureZeroSuppAll,
  Polyfold.EpGroupoid.not_isMeasureZeroSuppAny_orbitSupp,
  Polyfold.EpGroupoid.not_isMeasureZeroSupp_orbitSupp, Polyfold.isNull_transfer_mixed_dim]
#rt_overlap RoundTrip.V9_50.A_to_B [Polyfold.EpGroupoid.isMeasureZeroSuppAll_of_any,
  Polyfold.EpGroupoid.isMeasureZeroSuppAny_of_isMeasureZeroSupp, Polyfold.EpGroupoid.lemma_9_5_2,
  Polyfold.EpGroupoid.isSigmaIdeal_isMeasureZeroSupp,
  Polyfold.EpGroupoid.isSigmaIdeal_isMeasureZeroSuppAll,
  Polyfold.EpGroupoid.not_isMeasureZeroSuppAny_orbitSupp,
  Polyfold.EpGroupoid.not_isMeasureZeroSupp_orbitSupp, Polyfold.isNull_transfer_mixed_dim]
#print axioms RoundTrip.V9_50.A_to_B
#print axioms RoundTrip.V9_50.A_to_B_of_hyp
#print axioms RoundTrip.V9_50.B_to_A

end RoundTrip.V9_50
