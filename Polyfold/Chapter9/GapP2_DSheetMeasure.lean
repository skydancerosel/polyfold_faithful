import Polyfold.Chapter9.GapP2_DSheetEssential
import Polyfold.Chapter9.LocallyEquidimensional2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
§9.4, Lemmas 9.4.4, 9.4.6, p. 431, and §9.5, Definition 9.5.1, Lemma 9.5.2, p. 437, Definition
9.5.3, p. 438 (2017: Lemmas 9.13, 9.14, Definition 9.15, Lemma 9.16, Definition 9.16), for an
`n`-dimensional branched ep⁺-subgroupoid of an arbitrary ep-groupoid.

# Measure zero in `S = |supp(Θ)|` with the Lebesgue null sets of the sheets

The standing assumption of §9.5 is that `Θ` is `n`-dimensional.  Then every sheet of every local
branching structure of `Θ` is an `n`-dimensional submanifold
(`LocalBranchingStructure.isOfDim_of_isNDimensional`, from the independence of the tangent sums),
so the null sets of the `n`-dimensional submanifolds (`MPolyfold.sheetNullSets`) apply to all of
them and Lemma 9.5.2 holds as stated.

## What is formalized

* `LocalBranchingStructure.isOfDim_of_isNDimensional`: for an `n`-dimensional `Θ`, every local
  branching structure has `n`-dimensional sheets.
* **Lemmas 9.4.4 and 9.4.6** for the sheets of a local branching structure of an `n`-dimensional
  `Θ` (`lemma_9_4_4_of_isNDimensional`, `lemma_9_4_6_of_isNDimensional`).
* **Definition 9.5.1** with these null sets, `IsMeasureZeroH n Θ A`, and **Lemma 9.5.2**
  (`lemma_9_5_2_of_isNDimensional`): the preimages of `A` are null for a choice of local
  branching structures iff they are null for every local branching structure of `Θ`; for a tame
  `Θ`, also iff for a choice of tame structures (`lemma_9_5_2_tame`).
* `isSigmaIdeal_isMeasureZeroH`, `not_isMeasureZeroH_orbitSupp`, `lebesgueSigmaH`
  (**Definition 9.5.3** with these null sets) and `remark_9_5_3_H`.
* `MPolyfold.hNullSets`: the `m`-dimensional null sets as a `SheetNullSets` on any class of sets
  whose nonempty members are not `m`-null (for the boundaries `∂Mᵢ`, `m = n − 1`).
* **Across dimensions** (`isHNull_mixed_dim`): the axis `ℝ × 0` of `ℝ²` has `2`-dimensional
  measure zero and not `1`-dimensional measure zero; so for sheets of different dimensions the
  preimages of one set are null in one sheet and not in the other, and Lemma 9.5.2 without the
  standing assumption does not hold as we read it.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology MeasureTheory Metric Module TopologicalSpace
open scoped NNReal ENNReal symmDiff

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

variable (P) in
/-- **The `m`-dimensional null sets on a class of sets** whose nonempty members are not
`m`-null: a `SheetNullSets` (σ-ideal, local, the same on overlaps).  For the class of the
`n`-dimensional submanifolds and `m = n` this is `sheetNullSets`; for a class of boundaries
`∂Mᵢ` of `n`-dimensional sheets take `m = n − 1`. -/
def hNullSets (m : ℕ) (S : Set (Set X)) (hS : ∀ N ∈ S, N.Nonempty → ¬ P.IsHNull m N) :
    SheetNullSets S where
  IsNull N A := P.IsHNull m (A ∩ N)
  isNull_empty N := by rw [empty_inter]; exact isHNull_empty m
  isNull_mono h hA := h.mono (inter_subset_inter_left _ hA)
  isNull_iUnion h := by rw [iUnion_inter]; exact isHNull_iUnion h
  isNull_of_local N _ A h := isHNull_of_local fun z hz => by
    obtain ⟨V, hV, hzV, hn⟩ := h z hz.1
    exact ⟨V, hV, hzV, hn.mono fun w hw => ⟨⟨hw.1.1, hw.2⟩, hw.1.2⟩⟩
  isNull_transfer N _ N' _ C hC h := by
    have e : C ∩ N' = C ∩ N := by
      rw [inter_eq_left.2 fun w hw => (hC hw).2, inter_eq_left.2 fun w hw => (hC hw).1]
    rw [e]; exact h
  not_isNull_self N hN hne h := by
    rw [inter_self] at h
    exact hS N hN hne h

end MPolyfold

/-! ### Across dimensions -/

/-- The `2`-dimensional Hausdorff measure of the axis `ℝ × 0` of `ℝ²` is `0`. -/
theorem hNull_lineH : HNull (2 : ℝ) (lineH : Set (Fin 2 → ℝ)) := by
  rw [hNull_iff]
  have h : (μH[((Fintype.card (Fin 2) : ℕ) : ℝ)] : Measure (Fin 2 → ℝ)) = volume :=
    hausdorffMeasure_pi_real
  rw [Fintype.card_fin, Nat.cast_ofNat] at h
  rw [h]
  exact Measure.addHaar_submodule volume lineH lineH_ne_top

/-- **Measure zero across dimensions**: the axis `ℝ × 0` of `ℝ²` has `2`-dimensional measure
zero (it is a null set of the sheet `ℝ²`) and does not have `1`-dimensional measure zero (it is
a `1`-dimensional sheet).  So the preimage of one subset of `S` can be null in a sheet of one
dimension and not in a sheet of another: without sheets of one dimension Lemma 9.5.2 does not
hold as we read it. -/
theorem isHNull_mixed_dim :
    (rnPolyfold 2).IsHNull 2 EpGroupoid.axis2 ∧ ¬ (rnPolyfold 2).IsHNull 1 EpGroupoid.axis2 := by
  refine ⟨?_, MPolyfold.not_isHNull_of_hasDimAt EpGroupoid.axis2_isSubmanifoldOfDim.1
    (EpGroupoid.axis2_isSubmanifoldOfDim.2 0 EpGroupoid.zero_mem_axis2)⟩
  refine MPolyfold.isHNull_of_forall_exists_chart EpGroupoid.axis2_isSubmanifoldOfDim.1 subset_rfl
    fun z _ => ⟨rnChart 2 0, isChart_rnChart 0, mem_univ z, univ, isOpen_univ, mem_univ z, ?_⟩
  have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [h2]
  refine HNull.mono (t := (lineH : Set (Fin 2 → ℝ))) hNull_lineH ?_
  rintro _ ⟨r, ⟨⟨hr, -⟩, -⟩, rfl⟩
  change (r - 0) ∈ lineH
  rw [sub_zero]
  exact (mem_lineH).2 hr

namespace EpGroupoid

open MPolyfold

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ}

namespace LocalBranchingStructure

variable {x : Obj}

/-- **Every local branching structure of an `n`-dimensional `Θ` has `n`-dimensional sheets**
(the standing assumption of §9.5 reaches all structures): at `y ∈ Mᵢ` the tangent space `T_yMᵢ`
is a tangent space of an `n`-dimensional structure at `y`
(`hasDimAt_of_isOfDim`, from the independence of the tangent sums, Theorem 9.2.1 (1)). -/
theorem isOfDim_of_isNDimensional {n : ℕ} (hΘ : X.IsNDimensional Θ n)
    (B : X.LocalBranchingStructure Θ x) : B.IsOfDim n := fun i =>
  ⟨B.isSmoothSubmanifold i, fun y hy => by
    have hyU := B.subset_U i hy
    obtain ⟨B₀, hB₀⟩ := hΘ y ((B.mem_supp_iff hyU).2 ⟨i, hy⟩)
    have h := B₀.hasDimAt_of_isOfDim (B.restrictAt hyU) hB₀ ⟨i, hy⟩
    exact (hasDimAt_inter_isOpen_iff (B.isSmoothSubmanifold i) (B.isOpen_nbhdAt y)
      (B.mem_nbhdAt_self hyU)).1 h⟩

/-- **Lemma 9.4.4, 2021 p. 431 (2017: Lemma 9.13)**, for the sheets of a local branching
structure of an `n`-dimensional `Θ` on an arbitrary ep-groupoid: `K(i, i') = Mᵢ ∩ Mᵢ'` has the
same essential points as a subset of `Mᵢ` and of `Mᵢ'` (Definition 9.4.1 in M-polyfold charts).
For sheets of different dimensions it does not hold as we read it (`lemma_9_4_4_mixed_dim`). -/
theorem lemma_9_4_4_of_isNDimensional {n : ℕ} (hΘ : X.IsNDimensional Θ n)
    (B : X.LocalBranchingStructure Θ x) (i i' : B.ι) :
    X.PObj.chartEssentialSet (B.M i) (B.M i ∩ B.M i') =
      X.PObj.chartEssentialSet (B.M i') (B.M i' ∩ B.M i) :=
  lemma_9_4_4_chart (B.isOfDim_of_isNDimensional hΘ i) (B.isOfDim_of_isNDimensional hΘ i')

/-- **Lemma 9.4.6, 2021 p. 431 (2017: Lemma 9.14)**, for the sheets of a local branching
structure of an `n`-dimensional `Θ` on an arbitrary ep-groupoid: the non-essential points
`K(i, i')^{ne}` have measure zero (Definition 9.4.5 in M-polyfold charts). -/
theorem lemma_9_4_6_of_isNDimensional {n : ℕ} (hΘ : X.IsNDimensional Θ n)
    (B : X.LocalBranchingStructure Θ x) (i i' : B.ι) :
    X.PObj.IsHNull n
      ((B.M i ∩ B.M i') \ X.PObj.chartEssentialSet (B.M i) (B.M i ∩ B.M i')) :=
  lemma_9_4_6_chart (B.isOfDim_of_isNDimensional hΘ i) inter_subset_left

/-- Null preimages for the null sets of the `n`-dimensional sheets, spelled out. -/
theorem hasNullPreimages_sheetNullSets_iff {n : ℕ} (hΘ : X.IsNDimensional Θ n)
    (B : X.LocalBranchingStructure Θ x) (A : Set X.OrbitSpace) :
    B.HasNullPreimages (X.PObj.sheetNullSets n) A ↔
      ∀ i, X.PObj.IsHNull n (B.M i ∩ X.π ⁻¹' A) := by
  have e : ∀ i, B.M i ∩ X.π ⁻¹' A ∩ B.M i = B.M i ∩ X.π ⁻¹' A := fun i =>
    inter_eq_left.2 inter_subset_left
  constructor
  · rintro ⟨-, h⟩ i
    have := h i
    rwa [sheetNullSets_isNull_iff, e] at this
  · intro h
    refine ⟨fun i => B.isOfDim_of_isNDimensional hΘ i, fun i => ?_⟩
    rw [sheetNullSets_isNull_iff, e]
    exact h i

end LocalBranchingStructure

variable (X) in
/-- **Definition 9.5.1, 2021 p. 437 (2017: Definition 9.15)**, with the Lebesgue null sets of the
sheets: `A ⊆ S = |supp(Θ)|` has measure zero if at every `x ∈ supp(Θ)` some local branching
structure has preimages `Aᵢ = Mᵢ ∩ π⁻¹(A)` of `n`-dimensional measure zero (`IsHNull`,
Definition 9.4.5 in M-polyfold charts).  By `lemma_9_5_2_of_isNDimensional` the choice does not
matter. -/
def IsMeasureZeroH (n : ℕ) (Θ : Obj → ℚ) (A : Set X.OrbitSpace) : Prop :=
  ∀ x ∈ supp Θ, ∃ B : X.LocalBranchingStructure Θ x, ∀ i, X.PObj.IsHNull n (B.M i ∩ X.π ⁻¹' A)

theorem isMeasureZeroH_iff_any {n : ℕ} (hΘ : X.IsNDimensional Θ n) (A : Set X.OrbitSpace) :
    X.IsMeasureZeroH n Θ A ↔ X.IsMeasureZeroSuppAny (X.PObj.sheetNullSets n) Θ A :=
  forall₂_congr fun _ _ => exists_congr fun B =>
    (B.hasNullPreimages_sheetNullSets_iff hΘ A).symm

/-- **Lemma 9.5.2, 2021 p. 437 (2017: Lemma 9.16)**, for an `n`-dimensional `Θ` on an arbitrary
ep-groupoid: the definition of measure zero in `S` does not depend on the choice of the local
branching structures.  If at every point of `supp(Θ)` some local branching structure has null
preimages of `A`, then every local branching structure of `Θ` has. -/
theorem lemma_9_5_2_of_isNDimensional {n : ℕ} (hΘ : X.IsNDimensional Θ n)
    (A : Set X.OrbitSpace) :
    X.IsMeasureZeroH n Θ A ↔ ∀ x ∈ supp Θ, ∀ B : X.LocalBranchingStructure Θ x,
      ∀ i, X.PObj.IsHNull n (B.M i ∩ X.π ⁻¹' A) := by
  rw [isMeasureZeroH_iff_any hΘ]
  constructor
  · intro h x hx B
    exact (B.hasNullPreimages_sheetNullSets_iff hΘ A).1
      ⟨fun i => B.isOfDim_of_isNDimensional hΘ i,
        isMeasureZeroSuppAll_of_any _ h x hx B fun i => B.isOfDim_of_isNDimensional hΘ i⟩
  · intro h x hx
    obtain ⟨B, -⟩ := hΘ x hx
    exact ⟨B, (B.hasNullPreimages_sheetNullSets_iff hΘ A).2 (h x hx B)⟩

/-- A tame `n`-dimensional `Θ` satisfies the standing assumption `HasTameSheetsIn` for the class
of the `n`-dimensional submanifolds. -/
theorem hasTameSheetsIn_of_isNDimensional {n : ℕ} (hΘ : X.IsNDimensional Θ n)
    (hT : X.IsTameBranched Θ) :
    X.HasTameSheetsIn {N : Set Obj | X.PObj.IsSubmanifoldOfDim N n} Θ := fun x hx => by
  obtain ⟨B⟩ := hT x hx
  exact ⟨B, fun i => B.toLocalBranchingStructure.isOfDim_of_isNDimensional hΘ i⟩

/-- **Lemma 9.5.2 for a tame `n`-dimensional `Θ`** (the setting of §9.5): measure zero for a
choice of tame local branching structures (Definition 9.5.1 as in `IsMeasureZeroSupp`, "a
suitable `U(x)`" being a tame structure) is measure zero for a choice of local branching
structures, and so for all of them. -/
theorem lemma_9_5_2_tame {n : ℕ} (hΘ : X.IsNDimensional Θ n) (hT : X.IsTameBranched Θ)
    (A : Set X.OrbitSpace) :
    X.IsMeasureZeroSupp (X.PObj.sheetNullSets n) Θ A ↔ X.IsMeasureZeroH n Θ A := by
  rw [isMeasureZeroH_iff_any hΘ]
  exact (lemma_9_5_2 _ (hasTameSheetsIn_of_isNDimensional hΘ hT) A).1

/-- The sets of measure zero in `S` form a σ-ideal. -/
theorem isSigmaIdeal_isMeasureZeroH {n : ℕ} (hΘ : X.IsNDimensional Θ n) :
    IsSigmaIdeal {A : Set X.OrbitSpace | X.IsMeasureZeroH n Θ A} := by
  have he : ∀ A, X.IsMeasureZeroH n Θ A ↔
      X.IsMeasureZeroSuppAll (X.PObj.sheetNullSets n) Θ A := fun A => by
    rw [isMeasureZeroH_iff_any hΘ]
    refine ⟨isMeasureZeroSuppAll_of_any _, fun h x hx => ?_⟩
    obtain ⟨B, hB⟩ := hΘ x hx
    exact ⟨B, hB, h x hx B hB⟩
  have h := isSigmaIdeal_isMeasureZeroSuppAll (X.PObj.sheetNullSets n) (X := X) (Θ := Θ)
  exact ⟨(he ∅).2 h.empty_mem, fun hB hAB => (he _).2 (h.mono ((he _).1 hB) hAB),
    fun A hA => (he _).2 (h.iUnion_mem A fun k => (he _).1 (hA k))⟩

/-- **`S = |supp(Θ)|` does not have measure zero** when `supp(Θ) ≠ ∅`: a nonempty
`n`-dimensional sheet is not `n`-null (`not_isHNull_of_hasDimAt`). -/
theorem not_isMeasureZeroH_orbitSupp {n : ℕ} (hΘn : X.IsNDimensional Θ n)
    (hΘ : X.IsFunctorial Θ) (hne : (supp Θ).Nonempty) :
    ¬ X.IsMeasureZeroH n Θ (X.orbitSupp Θ) := fun h =>
  not_isMeasureZeroSuppAny_orbitSupp (X.PObj.sheetNullSets n) hΘ hne
    ((isMeasureZeroH_iff_any hΘn _).1 h)

variable (X) in
/-- **Definition 9.5.3, 2021 p. 438 (2017: Definition 9.16) (the canonical σ-algebra `L(S)`)**,
with the Lebesgue null sets of the sheets: the smallest σ-algebra on `S = |supp(Θ)|` containing
the Borel sets and the subsets of measure zero (`IsMeasureZeroH`). -/
@[instance_reducible] def lebesgueSigmaH (n : ℕ) (Θ : Obj → ℚ) :
    MeasurableSpace (X.orbitSupp Θ) :=
  borelNullSigma _ {A : Set (X.orbitSupp Θ) | X.IsMeasureZeroH n Θ (Subtype.val '' A)}

/-- **The remark after Definition 9.5.3** for `lebesgueSigmaH`: `K ∈ L(S)` iff `K` differs from a
Borel set by a set of measure zero. -/
theorem remark_9_5_3_H {n : ℕ} (hΘ : X.IsNDimensional Θ n) (K : Set (X.orbitSupp Θ)) :
    MeasurableSet[X.lebesgueSigmaH n Θ] K ↔
      ∃ B, MeasurableSet[borel _] B ∧ X.IsMeasureZeroH n Θ (Subtype.val '' (K ∆ B)) := by
  have h := isSigmaIdeal_isMeasureZeroH hΘ
  have hI : IsSigmaIdeal
      {A : Set (X.orbitSupp Θ) | X.IsMeasureZeroH n Θ (Subtype.val '' A)} := by
    refine ⟨?_, fun {A B} hB hAB => h.mono (B := Subtype.val '' B) hB (image_mono hAB),
      fun A hA => ?_⟩
    · change X.IsMeasureZeroH n Θ _
      rw [image_empty]
      exact h.empty_mem
    · change X.IsMeasureZeroH n Θ _
      rw [image_iUnion]
      exact h.iUnion_mem _ hA
  exact measurableSet_borelNullSigma_iff hI

/-- For a tame `n`-dimensional `Θ`, `lebesgueSigmaH` is the σ-algebra `L(S)` of
`Chapter9/Measure.lean` for the null sets of the `n`-dimensional sheets. -/
theorem lebesgueSigmaH_eq {n : ℕ} (hΘ : X.IsNDimensional Θ n) (hT : X.IsTameBranched Θ) :
    X.lebesgueSigmaH n Θ = X.lebesgueSigma (X.PObj.sheetNullSets n) Θ := by
  have e : {A : Set (X.orbitSupp Θ) | X.IsMeasureZeroH n Θ (Subtype.val '' A)} =
      X.measureZeroSets (X.PObj.sheetNullSets n) Θ := by
    ext A
    exact (lemma_9_5_2_tame hΘ hT _).symm
  change borelNullSigma _ _ = borelNullSigma _ _
  rw [e]

end EpGroupoid

end Polyfold
