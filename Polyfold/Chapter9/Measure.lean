import Polyfold.Chapter9.BranchingGeometry

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5 "Integration and Stokes" (2021 pp. 436–452; 2017: §9.5, pp. 322–331):
the measure-theoretic part, **Definition 9.5.1** (p. 437; 2017: Definition 9.15, p. 322),
**Lemma 9.5.2** (p. 437; 2017: Lemma 9.16, p. 322), **Definition 9.5.3** (p. 438; 2017:
Definition 9.16, p. 323) with the remark after it, and **Definition 9.5.14** (p. 448; 2017:
Definition 9.17, p. 327).  Numbers and pages are the 2021 text's, the 2017 ones in parentheses.
The isotropy part of Lemmas 9.5.9–9.5.11 and Proposition 9.5.13 is in
`Polyfold/Chapter9/MeasureEffective.lean`.

# Sets of measure zero in `|supp(Θ)|` and the σ-algebras `L(S)`, `L(∂S)`

## The text, paraphrased

(p. 437) `Θ` is an oriented, tame, compact branched ep⁺-subgroupoid of dimension `n`
(Definition 9.3.6) and `S = |supp(Θ)| ⊆ |X|`.  On a smooth `n`-manifold "measure zero" makes
sense (Definition 9.4.5).  A local branching structure `(Mᵢ, σᵢ)` on `U = U(x)` gives
`M_U = ⋃ Mᵢ` and `|M_U| ⊆ S`; for `A ⊆ S` let `Aᵢ ⊆ Mᵢ` be the preimage of `A ∩ |M_U|`.
(Definition 9.5.1) `A` has measure zero if for every `x ∈ supp(Θ)` and a choice of local
branching structure on a suitable `U(x)` all `Aᵢ` have measure zero.  (Lemma 9.5.2, cited from
the literature, no proof) This does not depend on the choice.  (Definition 9.5.3) `L(S)` is the
smallest σ-algebra on `S` containing the Borel sets `B(S)` and the sets of measure zero; it is
"obtained from `B(S)` by just adding the sets of measure zero".  (p. 448) For `K ⊆ |∂M_U|` the
preimages lie in `∂Mᵢ`; `Mᵢ` being tame, `(n-1)`-dimensional measure zero in the boundary faces
makes sense, which defines measure zero in `∂S = |supp(∂Θ)|`.  (Definition 9.5.14) `L(∂S)` is
the smallest σ-algebra containing `B(∂S)` and the subsets of `∂S` of measure zero.

## What is formalized

* `borelNullSigma` (Borel sets and a family `𝒩`), `IsSigmaIdeal`, `borelNullCompletion`,
  `measurableSet_borelNullSigma_iff` (for a σ-ideal `𝒩`, the generated σ-algebra is
  `{A | ∃ Borel B, A ∆ B ∈ 𝒩}`).
* `SheetNullSets`: null sets in the sheets of a class `S` of submanifolds;
  `MPolyfold.SheetMeasureGeometry` (a §9.4 `SheetGeometry` with the same three extra fields) and
  `toSheetNullSets`; `SheetNullSets.isNull_of_cover`.
* `IsMeasureZeroSupp` (**Definition 9.5.1**), with `IsMeasureZeroSuppAny`, `IsMeasureZeroSuppAll`,
  `HasTameSheetsIn`, `LocalBranchingStructure.HasNullPreimages` and its §9.4 form
  `hasNullPreimages_iff_isNullIn`.
* `lemma_9_5_2` (**Lemma 9.5.2**), from `isMeasureZeroSuppAll_of_any`; `isSigmaIdeal_*`,
  `not_isMeasureZeroSupp_orbitSupp` (`S ≠ ∅` is not null).
* `measureZeroSets`, `lebesgueSigma` (**Definition 9.5.3**), `remark_9_5_3` (the remark after it),
  `measurableSet_lebesgueSigma_of_isMeasureZeroSupp`.
* `IsMeasureZeroBoundary`, `IsMeasureZeroBoundaryAll`, `isMeasureZeroBoundaryAll_of` (the "well
  defined notion" of p. 448), `boundaryMeasureZeroSets`, `lebesgueSigmaBoundary`
  (**Definition 9.5.14**), `orbitSupp_boundaryTheta_subset`.
* Witnesses: `graphSheetMeasureGeometry` (the graph sheets of §9.4), Example 9.3.5's `theta935`
  with `hasTameSheetsIn_theta935`, `isMeasureZeroSupp_theta935_zero` and `lebesgueSigma_theta935`
  (a nonempty null set; `S ∈ L(S)` is not null); `planeNull`, `thetaPlane` (`Θ = 1` on `ℝ²`) and
  `exists_mem_lebesgueSigma_not_borel_thetaPlane` (a member of `L(S)` that is not Borel).

## What the text leaves implicit, and the choices made

* "Measure zero in `Mᵢ`" is an abstract `SheetNullSets` on a class `S` of sheets, the class of the
  `n`-dimensional submanifolds in mind; `SheetMeasureGeometry` ties it to §9.4's `SheetGeometry`.
  The field `isNull_transfer` (two sheets induce the same null sets on their intersection) is the
  content of Lemma 9.5.2: given it, the lemma holds for all choices (`lemma_9_5_2`).  It holds for
  one dimension and fails across dimensions (`isNull_transfer_mixed_dim`), so the lemma is proved
  for structures with sheets in one class, as for an `n`-dimensional `Θ`.
* "A suitable `U(x)`" is a `TameBranchingStructure` (natural `G_x`-action, properness, tame
  sheets); `HasTameSheetsIn` asks for one with sheets in `S` at every point (for `ℝⁿ`:
  `hasTameSheetsIn_trivial_rn`).  Compactness and orientation are not used.
* The remark after Definition 9.5.3 is read as the completion `K ∆ B` null; the literal "`B ∪ N`"
  would need Borel null hulls.
* `(n-1)`-dimensional measure zero in `∂Mᵢ` is a second `SheetNullSets` on the boundaries
  (`submanifoldBoundary`); the face-by-face description is not formalized in this file.  No `∂S`
  witness with a nonempty boundary is given here (the plane examples have no boundary).  Since
  2026-11-12: face by face `IsFaceNull`, the case `n = 1` and the half-line witness with `∂S ≠ ∅`
  are in `GapP2_E2BoundaryNull.lean`; the null sets of the sheets of a general M-polyfold are
  concrete (`MPolyfold.IsHNull`, `MPolyfold.sheetNullSets`, `GapP2_DSheetNull.lean`), and Lemma
  9.5.2 holds for every local branching structure of an `n`-dimensional `Θ`
  (`lemma_9_5_2_of_isNDimensional`, `GapP2_DSheetMeasure.lean`).

## Not formalized

Since 2026-11-12 the items below are proved for an abstract integration of forms over oriented
sheets (`SheetIntegration`, `GapP2_E1_*.lean`: Theorems 9.5.4, 9.5.5, Definition 9.5.6, (9.21),
Lemmas 9.5.7, 9.5.9–9.5.11, Proposition 9.5.13 (1)), Theorems 9.5.15–9.5.16 from their local
expressions (`theorem_9_5_15_of_overlap`) and Theorems 9.5.17–9.5.18 from the localization of
the proof (`theorem_9_5_17_of_localization`, `GapP2_E2*.lean`); the concrete integral over the
sheets is not built.  In this file:
forms, integrals and the measures `μ_ω` (gaps G.74, G.80): Theorems 9.5.4, 9.5.5, 9.5.15–9.5.18,
Definition 9.5.6, (9.21), (9.22), Lemma 9.5.7 (its combinatorics is `proposition_9_4_10`),
Remarks 9.5.8, 9.5.12, 9.5.19, 9.5.20.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology MeasureTheory Manifold Module
open scoped symmDiff ContDiff Cardinal

noncomputable section

namespace Polyfold

universe u

/-! ### Borel sets modified by null sets -/

section BorelNull

variable (T : Type*) [TopologicalSpace T]

/-- The σ-algebra on `T` generated by the Borel sets and a family `𝒩` of (null) sets. -/
@[instance_reducible] def borelNullSigma (𝒩 : Set (Set T)) : MeasurableSpace T :=
  MeasurableSpace.generateFrom ({A | MeasurableSet[borel T] A} ∪ 𝒩)

variable {T}

/-- A **σ-ideal** of subsets of `T`: it contains `∅`, is closed under subsets and countable
unions. -/
structure IsSigmaIdeal (𝒩 : Set (Set T)) : Prop where
  empty_mem : ∅ ∈ 𝒩
  mono : ∀ {A B : Set T}, B ∈ 𝒩 → A ⊆ B → A ∈ 𝒩
  iUnion_mem : ∀ A : ℕ → Set T, (∀ k, A k ∈ 𝒩) → (⋃ k, A k) ∈ 𝒩

theorem borel_le_borelNullSigma (𝒩 : Set (Set T)) : borel T ≤ borelNullSigma T 𝒩 :=
  fun _ hA => MeasurableSpace.measurableSet_generateFrom (Or.inl hA)

theorem measurableSet_borelNullSigma_of_mem {𝒩 : Set (Set T)} {A : Set T} (hA : A ∈ 𝒩) :
    MeasurableSet[borelNullSigma T 𝒩] A :=
  MeasurableSpace.measurableSet_generateFrom (Or.inr hA)

omit [TopologicalSpace T] in
theorem symmDiff_iUnion_subset (A B : ℕ → Set T) :
    (⋃ k, A k) ∆ (⋃ k, B k) ⊆ ⋃ k, A k ∆ B k := by
  intro z hz
  rw [mem_symmDiff] at hz
  rcases hz with ⟨hA, hB⟩ | ⟨hB, hA⟩
  · obtain ⟨k, hk⟩ := mem_iUnion.1 hA
    exact mem_iUnion.2 ⟨k, mem_symmDiff.2 (Or.inl ⟨hk, fun h => hB (mem_iUnion.2 ⟨k, h⟩)⟩)⟩
  · obtain ⟨k, hk⟩ := mem_iUnion.1 hB
    exact mem_iUnion.2 ⟨k, mem_symmDiff.2 (Or.inr ⟨hk, fun h => hA (mem_iUnion.2 ⟨k, h⟩)⟩)⟩

/-- The sets differing from a Borel set by a member of the σ-ideal `𝒩` form a σ-algebra. -/
@[instance_reducible] def borelNullCompletion {𝒩 : Set (Set T)} (h𝒩 : IsSigmaIdeal 𝒩) :
    MeasurableSpace T where
  MeasurableSet' A := ∃ B, MeasurableSet[borel T] B ∧ A ∆ B ∈ 𝒩
  measurableSet_empty := ⟨∅, @MeasurableSet.empty T (borel T), by
    rw [symmDiff_self]; exact h𝒩.empty_mem⟩
  measurableSet_compl _ := fun ⟨B, hB, h⟩ => ⟨Bᶜ, hB.compl, by rwa [compl_symmDiff_compl]⟩
  measurableSet_iUnion A hA := by
    choose B hB h using hA
    exact ⟨⋃ k, B k, MeasurableSet.iUnion hB,
      h𝒩.mono (h𝒩.iUnion_mem _ h) (symmDiff_iUnion_subset A B)⟩

/-- **Borel sets modified by null sets**: if `𝒩` is a σ-ideal, the σ-algebra generated by the
Borel sets and `𝒩` consists of the sets `A` with `A ∆ B ∈ 𝒩` for a Borel set `B`. -/
theorem measurableSet_borelNullSigma_iff {𝒩 : Set (Set T)} (h𝒩 : IsSigmaIdeal 𝒩) {A : Set T} :
    MeasurableSet[borelNullSigma T 𝒩] A ↔ ∃ B, MeasurableSet[borel T] B ∧ A ∆ B ∈ 𝒩 := by
  constructor
  · intro hA
    have hle : borelNullSigma T 𝒩 ≤ borelNullCompletion h𝒩 := by
      refine MeasurableSpace.generateFrom_le ?_
      rintro C (hC | hC)
      · exact ⟨C, hC, by rw [symmDiff_self]; exact h𝒩.empty_mem⟩
      · refine ⟨∅, @MeasurableSet.empty T (borel T), ?_⟩
        have h0 : C ∆ (∅ : Set T) = C := symmDiff_bot C
        rwa [h0]
    exact hle _ hA
  · rintro ⟨B, hB, hAB⟩
    have h1 : A \ B ∈ 𝒩 := h𝒩.mono hAB fun z hz => mem_symmDiff.2 (Or.inl hz)
    have h2 : B \ A ∈ 𝒩 := h𝒩.mono hAB fun z hz => mem_symmDiff.2 (Or.inr hz)
    have hA : A = (B \ (B \ A)) ∪ (A \ B) := by
      ext z
      by_cases hzA : z ∈ A <;> by_cases hzB : z ∈ B <;> simp [hzA, hzB]
    rw [hA]
    exact ((borel_le_borelNullSigma 𝒩 _ hB).diff (measurableSet_borelNullSigma_of_mem h2)).union
      (measurableSet_borelNullSigma_of_mem h1)

end BorelNull

/-! ### Null sets of a class of sheets -/

section SheetNull

variable {X : Type u} [TopologicalSpace X]

/-- **The sets of measure zero in the sheets of a class `S`** (Definition 9.4.5, used in
Definition 9.5.1): `IsNull N A` means "`A ∩ N` has measure zero in the sheet `N`".  The fields:
null sets form a σ-ideal in every sheet (`isNull_empty`, `isNull_mono`, `isNull_iUnion`); being
null is local (`isNull_of_local`: null near each of its points); two sheets of `S` induce the same
null sets on their intersection (`isNull_transfer`); a nonempty sheet is not null in itself
(`not_isNull_self`).  The transfer property holds for submanifolds of one dimension (the class of
an `n`-dimensional `Θ`), not across dimensions (`isNull_transfer_mixed_dim`). -/
structure SheetNullSets (S : Set (Set X)) where
  /-- `A` has measure zero in the sheet `N`. -/
  IsNull : Set X → Set X → Prop
  isNull_empty : ∀ N, IsNull N ∅
  isNull_mono : ∀ {N A A'}, IsNull N A' → A ⊆ A' → IsNull N A
  isNull_iUnion : ∀ {N} {A : ℕ → Set X}, (∀ k, IsNull N (A k)) → IsNull N (⋃ k, A k)
  isNull_of_local : ∀ N ∈ S, ∀ A : Set X,
    (∀ z ∈ A, ∃ V, IsOpen V ∧ z ∈ V ∧ IsNull N (A ∩ V)) → IsNull N A
  isNull_transfer : ∀ N ∈ S, ∀ N' ∈ S, ∀ C, C ⊆ N ∩ N' → IsNull N C → IsNull N' C
  not_isNull_self : ∀ N ∈ S, N.Nonempty → ¬ IsNull N N

namespace SheetNullSets

variable {S : Set (Set X)} (G : SheetNullSets S)

theorem isNull_iUnion_countable {κ : Type*} [Countable κ] {N : Set X} {A : κ → Set X}
    (h : ∀ k, G.IsNull N (A k)) : G.IsNull N (⋃ k, A k) := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · rw [iUnion_of_empty]
    exact G.isNull_empty N
  · obtain ⟨f, hf⟩ := exists_surjective_nat κ
    rw [← hf.iUnion_comp]
    exact G.isNull_iUnion fun n => h (f n)

theorem isNull_union {N A A' : Set X} (h : G.IsNull N A) (h' : G.IsNull N A') :
    G.IsNull N (A ∪ A') := by
  rw [union_eq_iUnion]
  exact G.isNull_iUnion_countable fun b => by cases b <;> assumption

/-- **The covering criterion** (the core of Lemma 9.5.2): a subset `C` of a sheet `N ∈ S` is
null in `N` if near each of its points it is covered by finitely many sheets `F k ∈ S` in which
it is null. -/
theorem isNull_of_cover {N C : Set X} (hN : N ∈ S) (hC : C ⊆ N)
    (h : ∀ z ∈ C, ∃ V, IsOpen V ∧ z ∈ V ∧ ∃ (κ : Type u) (_ : Finite κ) (F : κ → Set X),
      (∀ k, F k ∈ S) ∧ C ∩ V ⊆ ⋃ k, F k ∧ ∀ k, G.IsNull (F k) (C ∩ F k)) :
    G.IsNull N C := by
  refine G.isNull_of_local N hN C fun z hz => ?_
  obtain ⟨V, hV, hzV, κ, _, F, hFS, hcov, hnull⟩ := h z hz
  refine ⟨V, hV, hzV, G.isNull_mono (G.isNull_iUnion_countable (A := fun k => C ∩ F k)
    fun k => ?_) ?_⟩
  · exact G.isNull_transfer _ (hFS k) _ hN _ (fun w hw => ⟨hw.2, hC hw.1⟩) (hnull k)
  · intro w hw
    obtain ⟨k, hk⟩ := mem_iUnion.1 (hcov hw)
    exact mem_iUnion.2 ⟨k, hw.1, hk⟩

end SheetNullSets

end SheetNull

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

variable (P) in
/-- **A sheet geometry with the measure-theoretic properties of §9.5**: a `SheetGeometry` of §9.4
(essential points, null sets, Lemmas 9.4.4 and 9.4.6) whose null sets are closed under countable
unions, local, and induced alike by two sheets on their intersection. -/
structure SheetMeasureGeometry (S : Set (Set X)) extends P.SheetGeometry S where
  isNull_iUnion : ∀ {N} {A : ℕ → Set X}, (∀ k, IsNull N (A k)) → IsNull N (⋃ k, A k)
  isNull_of_local : ∀ N ∈ S, ∀ A : Set X,
    (∀ z ∈ A, ∃ V, IsOpen V ∧ z ∈ V ∧ IsNull N (A ∩ V)) → IsNull N A
  isNull_transfer : ∀ N ∈ S, ∀ N' ∈ S, ∀ C, C ⊆ N ∩ N' → IsNull N C → IsNull N' C

/-- The null sets of a `SheetMeasureGeometry`. -/
def SheetMeasureGeometry.toSheetNullSets {S : Set (Set X)} (G : P.SheetMeasureGeometry S) :
    SheetNullSets S where
  IsNull := G.IsNull
  isNull_empty := G.isNull_empty
  isNull_mono := G.isNull_mono
  isNull_iUnion := G.isNull_iUnion
  isNull_of_local := G.isNull_of_local
  isNull_transfer := G.isNull_transfer
  not_isNull_self := G.not_isNull_self

end MPolyfold

/-! ### Definition 9.5.1 and Lemma 9.5.2 -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {S : Set (Set Obj)} (G : SheetNullSets S) {Θ : Obj → ℚ}

namespace LocalBranchingStructure

variable {x : Obj}

/-- The sheets of `B` lie in `S` and the preimages `Aᵢ = Mᵢ ∩ π⁻¹(A)` of `A ⊆ |X|` under the
canonical maps `Mᵢ → |M_U|` have measure zero in `Mᵢ` (Definition 9.5.1). -/
def HasNullPreimages (B : X.LocalBranchingStructure Θ x) (A : Set X.OrbitSpace) : Prop :=
  (∀ i, B.M i ∈ S) ∧ ∀ i, G.IsNull (B.M i) (B.M i ∩ X.π ⁻¹' A)

end LocalBranchingStructure

variable (X)

/-- **Definition 9.5.1, 2021 p. 437 (2017: Definition 9.15, p. 322)**: `A ⊆ S = |supp(Θ)|` has
**measure zero** if for every `x ∈ supp(Θ)` a choice of local branching structure on a suitable
`U(x)` (with the natural `G_x`-action and the properness property, the sheets tame:
`TameBranchingStructure`, Definition 9.3.6), with sheets in `S`, has preimages `Aᵢ ⊆ Mᵢ` of
measure zero.  (The condition only involves `A ∩ S`.) -/
def IsMeasureZeroSupp (Θ : Obj → ℚ) (A : Set X.OrbitSpace) : Prop :=
  ∀ x ∈ supp Θ, ∃ B : X.TameBranchingStructure Θ x,
    B.toLocalBranchingStructure.HasNullPreimages G A

/-- Definition 9.5.1 with an arbitrary local branching structure at every point. -/
def IsMeasureZeroSuppAny (Θ : Obj → ℚ) (A : Set X.OrbitSpace) : Prop :=
  ∀ x ∈ supp Θ, ∃ B : X.LocalBranchingStructure Θ x, B.HasNullPreimages G A

/-- Definition 9.5.1 for every local branching structure with sheets in `S`. -/
def IsMeasureZeroSuppAll (Θ : Obj → ℚ) (A : Set X.OrbitSpace) : Prop :=
  ∀ x ∈ supp Θ, ∀ B : X.LocalBranchingStructure Θ x, (∀ i, B.M i ∈ S) →
    ∀ i, G.IsNull (B.M i) (B.M i ∩ X.π ⁻¹' A)

/-- Every point of `supp(Θ)` has a tame local branching structure (Definition 9.3.6) with sheets in
the class `S` (the standing assumption of §9.5: `Θ` tame, its sheets of the class carrying the
null sets). -/
def HasTameSheetsIn (S : Set (Set Obj)) (Θ : Obj → ℚ) : Prop :=
  ∀ x ∈ supp Θ, ∃ B : X.TameBranchingStructure Θ x, ∀ i, B.M i ∈ S

variable {X}

/-- **The core of Lemma 9.5.2**: if some local branching structure at every point of `supp(Θ)`
has null preimages of `A`, then every local branching structure with sheets in `S` has. -/
theorem isMeasureZeroSuppAll_of_any {A : Set X.OrbitSpace} (h : X.IsMeasureZeroSuppAny G Θ A) :
    X.IsMeasureZeroSuppAll G Θ A := by
  intro x' _ B' hB'S j
  refine G.isNull_of_cover (hB'S j) inter_subset_left fun z hz => ?_
  have hsupp : ∀ {w}, w ∈ B'.M j → w ∈ supp Θ := fun hw =>
    (B'.mem_supp_iff (B'.subset_U j hw)).2 ⟨j, hw⟩
  obtain ⟨B, hBS, hBnull⟩ := h z (hsupp hz.1)
  refine ⟨B.U, B.isOpen_U, B.mem_U, B.ι, inferInstance, B.M, hBS, fun w hw => ?_,
    fun i => G.isNull_mono (hBnull i) fun w hw => ⟨hw.2, hw.1.2⟩⟩
  exact mem_iUnion.2 ((B.mem_supp_iff hw.2).1 (hsupp hw.1.1))

theorem isMeasureZeroSuppAny_of_isMeasureZeroSupp {A : Set X.OrbitSpace}
    (h : X.IsMeasureZeroSupp G Θ A) : X.IsMeasureZeroSuppAny G Θ A := fun x hx => by
  obtain ⟨B, hB⟩ := h x hx
  exact ⟨B.toLocalBranchingStructure, hB⟩

/-- **Lemma 9.5.2, 2021 p. 437 (2017: Lemma 9.16, p. 322)**: the notion of measure zero does not
depend on the choice of the local branching structures.  If every point of `supp(Θ)` has a tame
local branching structure with sheets in `S`, then "null preimages for a choice of tame
structures", "for a choice of structures" and "for all structures with sheets in `S`" agree. -/
theorem lemma_9_5_2 (hS : X.HasTameSheetsIn S Θ) (A : Set X.OrbitSpace) :
    (X.IsMeasureZeroSupp G Θ A ↔ X.IsMeasureZeroSuppAny G Θ A) ∧
      (X.IsMeasureZeroSuppAny G Θ A ↔ X.IsMeasureZeroSuppAll G Θ A) := by
  have hAll : X.IsMeasureZeroSuppAll G Θ A → X.IsMeasureZeroSupp G Θ A := fun h x hx => by
    obtain ⟨B, hBS⟩ := hS x hx
    exact ⟨B, hBS, h x hx _ hBS⟩
  exact ⟨⟨isMeasureZeroSuppAny_of_isMeasureZeroSupp G,
      fun h => hAll (isMeasureZeroSuppAll_of_any G h)⟩,
    ⟨isMeasureZeroSuppAll_of_any G,
      fun h => isMeasureZeroSuppAny_of_isMeasureZeroSupp G (hAll h)⟩⟩


/-- The sets of measure zero for all structures form a σ-ideal of subsets of `|X|`. -/
theorem isSigmaIdeal_isMeasureZeroSuppAll :
    IsSigmaIdeal {A : Set X.OrbitSpace | X.IsMeasureZeroSuppAll G Θ A} where
  empty_mem _ _ B _ i := by
    rw [preimage_empty, inter_empty]
    exact G.isNull_empty _
  mono hB hAB x hx B' hS i :=
    G.isNull_mono (hB x hx B' hS i) (inter_subset_inter_right _ (preimage_mono hAB))
  iUnion_mem A hA x hx B hS i := by
    rw [preimage_iUnion, inter_iUnion]
    exact G.isNull_iUnion fun k => hA k x hx B hS i

/-- Under the standing assumption, the sets of measure zero (Definition 9.5.1) form a σ-ideal. -/
theorem isSigmaIdeal_isMeasureZeroSupp (hS : X.HasTameSheetsIn S Θ) :
    IsSigmaIdeal {A : Set X.OrbitSpace | X.IsMeasureZeroSupp G Θ A} := by
  have he : ∀ A, X.IsMeasureZeroSupp G Θ A ↔ X.IsMeasureZeroSuppAll G Θ A := fun A =>
    ((lemma_9_5_2 G hS A).1).trans (lemma_9_5_2 G hS A).2
  have h := isSigmaIdeal_isMeasureZeroSuppAll G (X := X) (Θ := Θ)
  exact ⟨(he ∅).2 h.empty_mem, fun hB hAB => (he _).2 (h.mono ((he _).1 hB) hAB),
    fun A hA => (he _).2 (h.iUnion_mem A fun k => (he _).1 (hA k))⟩

/-- **`|supp(Θ)|` itself does not have measure zero** when `supp(Θ) ≠ ∅` (for any choice of
local branching structures): the preimage of `S` in a sheet is the whole sheet. -/
theorem not_isMeasureZeroSuppAny_orbitSupp (hΘ : X.IsFunctorial Θ) (hne : (supp Θ).Nonempty) :
    ¬ X.IsMeasureZeroSuppAny G Θ (X.orbitSupp Θ) := by
  intro h
  obtain ⟨x, hx⟩ := hne
  obtain ⟨B, hBS, hBnull⟩ := h x hx
  obtain ⟨i, hi⟩ := (B.mem_supp_iff B.mem_U).1 hx
  have hsub : B.M i ⊆ B.M i ∩ X.π ⁻¹' X.orbitSupp Θ := fun w hw => ⟨hw, by
    rw [preimage_π_orbitSupp hΘ]
    exact (B.mem_supp_iff (B.subset_U i hw)).2 ⟨i, hw⟩⟩
  exact G.not_isNull_self _ (hBS i) ⟨x, hi⟩ (G.isNull_mono (hBnull i) hsub)

theorem not_isMeasureZeroSupp_orbitSupp (hΘ : X.IsFunctorial Θ) (hne : (supp Θ).Nonempty) :
    ¬ X.IsMeasureZeroSupp G Θ (X.orbitSupp Θ) := fun h =>
  not_isMeasureZeroSuppAny_orbitSupp G hΘ hne (isMeasureZeroSuppAny_of_isMeasureZeroSupp G h)

/-- **The link with §9.4**: for a `SheetMeasureGeometry`, null preimages are `IsNullIn` (measure
zero in `M_U` in the sense of Lemma 9.4.8 and Proposition 9.4.9) of `π⁻¹(A)`. -/
theorem LocalBranchingStructure.hasNullPreimages_iff_isNullIn
    (G : X.PObj.SheetMeasureGeometry S) {x : Obj} (B : X.LocalBranchingStructure Θ x)
    (hBS : ∀ i, B.M i ∈ S) (A : Set X.OrbitSpace) :
    B.HasNullPreimages G.toSheetNullSets A ↔ G.toSheetGeometry.IsNullIn B.M (X.π ⁻¹' A) := by
  refine ⟨fun h i => ?_, fun h => ⟨hBS, fun i => ?_⟩⟩
  · rw [inter_comm]; exact h.2 i
  · change G.IsNull _ _
    rw [inter_comm]; exact h i

/-! ### Definition 9.5.3 and the remark after it -/

variable (X) in
/-- The subsets of measure zero of `S = |supp(Θ)|` (Definition 9.5.1), as subsets of the
subspace `S`. -/
def measureZeroSets (Θ : Obj → ℚ) : Set (Set (X.orbitSupp Θ)) :=
  {A | X.IsMeasureZeroSupp G Θ (Subtype.val '' A)}

variable (X) in
/-- **Definition 9.5.3, 2021 p. 438 (2017: Definition 9.16, p. 323) (the canonical σ-algebra
`L(S)`)**: the smallest σ-algebra on `S = |supp(Θ)|` containing the Borel σ-algebra `B(S)` and
all subsets of `S` of measure zero (Definition 9.5.1). -/
@[instance_reducible] def lebesgueSigma (Θ : Obj → ℚ) : MeasurableSpace (X.orbitSupp Θ) :=
  borelNullSigma _ (X.measureZeroSets G Θ)

theorem isSigmaIdeal_measureZeroSets (hS : X.HasTameSheetsIn S Θ) :
    IsSigmaIdeal (X.measureZeroSets G Θ) := by
  have h := isSigmaIdeal_isMeasureZeroSupp G hS
  refine ⟨?_, fun hB hAB => h.mono hB (image_mono hAB), fun A hA => ?_⟩
  · change X.IsMeasureZeroSupp G Θ _
    rw [image_empty]
    exact h.empty_mem
  · change X.IsMeasureZeroSupp G Θ _
    rw [image_iUnion]
    exact h.iUnion_mem _ hA

/-- **The remark after Definition 9.5.3, 2021 p. 438 (2017: p. 323)** ("`L(S)` is obtained
from `B(S)` by just adding the sets of measure zero"), read as the standard completion: under the
standing assumption, `K ∈ L(S)` iff `K` differs from a Borel set `B` by a set `K ∆ B` of measure
zero. -/
theorem remark_9_5_3 (hS : X.HasTameSheetsIn S Θ) (K : Set (X.orbitSupp Θ)) :
    MeasurableSet[X.lebesgueSigma G Θ] K ↔
      ∃ B, MeasurableSet[borel _] B ∧ X.IsMeasureZeroSupp G Θ (Subtype.val '' (K ∆ B)) :=
  measurableSet_borelNullSigma_iff (isSigmaIdeal_measureZeroSets G hS)

/-- Every set of measure zero lies in `L(S)`. -/
theorem measurableSet_lebesgueSigma_of_isMeasureZeroSupp {K : Set (X.orbitSupp Θ)}
    (hK : X.IsMeasureZeroSupp G Θ (Subtype.val '' K)) : MeasurableSet[X.lebesgueSigma G Θ] K :=
  measurableSet_borelNullSigma_of_mem hK

/-! ### Definition 9.5.14: the σ-algebra `L(∂S)` -/

section Boundary

variable {S' : Set (Set Obj)} (G' : SheetNullSets S')

variable (X) in
/-- **`(n-1)`-dimensional measure zero in `∂S = |supp(∂Θ)|`** (2021 p. 448, before Definition
9.5.14): `K ⊆ ∂S` has measure zero if for every `x ∈ supp(∂Θ)` a choice of tame local branching
structure of `Θ` on `U(x)` has boundaries `∂Mᵢ` (`submanifoldBoundary`) in the class `S'` and
the preimages `Kᵢ = ∂Mᵢ ∩ π⁻¹(K)` have measure zero in `∂Mᵢ`.  "Measure zero in `∂Mᵢ`" (in every
boundary face, `(n-1)`-dimensional Lebesgue measure) is the null-set system `G'` of the class
`S'` of the boundaries. -/
def IsMeasureZeroBoundary (Θ : Obj → ℚ) (K : Set X.OrbitSpace) : Prop :=
  ∀ x ∈ supp (X.boundaryTheta Θ), ∃ B : X.TameBranchingStructure Θ x,
    (∀ i, X.PObj.submanifoldBoundary (B.M i) ∈ S') ∧
      ∀ i, G'.IsNull (X.PObj.submanifoldBoundary (B.M i))
        (X.PObj.submanifoldBoundary (B.M i) ∩ X.π ⁻¹' K)

variable (X) in
/-- The boundary notion for every local branching structure with boundaries in `S'`. -/
def IsMeasureZeroBoundaryAll (Θ : Obj → ℚ) (K : Set X.OrbitSpace) : Prop :=
  ∀ x ∈ supp (X.boundaryTheta Θ), ∀ B : X.LocalBranchingStructure Θ x,
    (∀ i, X.PObj.submanifoldBoundary (B.M i) ∈ S') →
      ∀ i, G'.IsNull (X.PObj.submanifoldBoundary (B.M i))
        (X.PObj.submanifoldBoundary (B.M i) ∩ X.π ⁻¹' K)

open scoped Classical in
theorem exists_mem_of_sum_pos {ι : Type*} [Fintype ι] {p : ι → Prop} {σ : ι → ℚ}
    (h : 0 < ∑ i with p i, σ i) : ∃ i, p i := by
  obtain ⟨i, hi, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
  exact ⟨i, (Finset.mem_filter.1 hi).2⟩

/-- **"There is a well-defined notion of a subset of `∂S` to be of `(n-1)`-dimensional measure
zero"** (2021 p. 448): if a choice of tame structures has null boundary preimages of `K`, then
so has every local branching structure with boundaries in `S'` (given Theorem 9.2.1's
independence of `TΘ`, through which `∂Θ` is defined). -/
theorem isMeasureZeroBoundaryAll_of (hind : X.HasIndependentTangentSums Θ) {K : Set X.OrbitSpace}
    (h : X.IsMeasureZeroBoundary G' Θ K) : X.IsMeasureZeroBoundaryAll G' Θ K := by
  classical
  intro x' _ B' hB'S j
  have hpos : ∀ {w}, w ∈ X.PObj.submanifoldBoundary (B'.M j) → w ∈ supp (X.boundaryTheta Θ) :=
    fun {w} hw => by
      have hwM : w ∈ B'.M j := by obtain ⟨-, hw', -⟩ := hw; exact hw'
      change 0 < X.boundaryTheta Θ w
      rw [X.boundaryTheta_eq hind B' (B'.subset_U j hwM)]
      exact Finset.sum_pos' (fun i _ => (B'.σ_pos i).le) ⟨j, by simp [hw], B'.σ_pos j⟩
  refine G'.isNull_of_cover (hB'S j) inter_subset_left fun z hz => ?_
  obtain ⟨B, hBS, hBnull⟩ := h z (hpos hz.1)
  refine ⟨B.U, B.isOpen_U, B.mem_U, B.ι, inferInstance,
    fun i => X.PObj.submanifoldBoundary (B.M i), hBS, fun w hw => ?_,
    fun i => G'.isNull_mono (hBnull i) fun w hw => ⟨hw.2, hw.1.2⟩⟩
  have h1 := hpos hw.1.1
  change 0 < X.boundaryTheta Θ w at h1
  rw [X.boundaryTheta_eq hind B.toLocalBranchingStructure hw.2] at h1
  exact mem_iUnion.2 (exists_mem_of_sum_pos h1)

variable (X) in
/-- The subsets of measure zero of `∂S = |supp(∂Θ)|`, as subsets of the subspace `∂S`. -/
def boundaryMeasureZeroSets (Θ : Obj → ℚ) : Set (Set (X.orbitSupp (X.boundaryTheta Θ))) :=
  {K | X.IsMeasureZeroBoundary G' Θ (Subtype.val '' K)}

variable (X) in
/-- **Definition 9.5.14, 2021 p. 448 (2017: Definition 9.17, p. 327) (the canonical σ-algebra
`L(∂S)`)**: the smallest σ-algebra on `∂S = |supp(∂Θ)|` containing the Borel σ-algebra `B(∂S)`
and all subsets of `∂S` of measure zero. -/
@[instance_reducible] def lebesgueSigmaBoundary (Θ : Obj → ℚ) :
    MeasurableSpace (X.orbitSupp (X.boundaryTheta Θ)) :=
  borelNullSigma _ (X.boundaryMeasureZeroSets G' Θ)

/-- `∂S ⊆ S` (2021 p. 448): `supp(∂Θ) ⊆ supp(Θ)`. -/
theorem orbitSupp_boundaryTheta_subset : X.orbitSupp (X.boundaryTheta Θ) ⊆ X.orbitSupp Θ := by
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨y, ?_, rfl⟩
  by_contra h
  exact lt_irrefl (0 : ℚ) (by
    have := X.boundaryTheta_eq_zero_of_not_mem_supp (Θ := Θ) h
    change 0 < X.boundaryTheta Θ y at hy
    rwa [this] at hy)

end Boundary

end EpGroupoid

/-! ### Witnesses -/

open EpGroupoid MPolyfold

section Witnesses

/-! #### Tools: null sets of Definition 9.4.5 -/

section Tools

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **Definition 9.4.5 is local** (for the image of a second countable space): if every point of
`A` has an open neighbourhood `V` with `p(A ∩ V)` of measure zero, then `p(A)` has measure zero. -/
theorem isMeasureZero_image_of_local {Z : Type*} [TopologicalSpace Z] [SecondCountableTopology Z]
    (p : Z → M) {A : Set Z} (h : ∀ z ∈ A, ∃ V, IsOpen V ∧ z ∈ V ∧ IsMeasureZero I (p '' (A ∩ V))) :
    IsMeasureZero I (p '' A) := by
  choose V hV hzV hnull using h
  obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun z : A => V z.1 z.2)
    fun z => hV z.1 z.2
  have := hT.to_subtype
  refine (isMeasureZero_iUnion (fun z : T => hnull z.1.1 z.1.2)).mono ?_
  rintro _ ⟨w, hw, rfl⟩
  have hw' : w ∈ ⋃ z : A, V z.1 z.2 := mem_iUnion.2 ⟨⟨w, hw⟩, hzV w hw⟩
  rw [← hTU] at hw'
  obtain ⟨z, hzT, hwz⟩ := mem_iUnion₂.1 hw'
  exact mem_iUnion.2 ⟨⟨z, hzT⟩, w, ⟨hw, hwz⟩, rfl⟩

/-- A subsingleton has measure zero (Definition 9.4.5) when the Lebesgue measure has no atoms. -/
theorem isMeasureZero_of_subsingleton [NullSingletonClass (volume : Measure E)] {K : Set M}
    (hK : K.Subsingleton) : IsMeasureZero I K := fun _ _ =>
  ((hK.anti inter_subset_right).image _).measure_zero volume

end Tools

/-- In the model space `ℝ²`, Definition 9.4.5 is `volume K = 0`. -/
theorem isMeasureZero_rn2_iff {K : Set (Fin 2 → ℝ)} :
    IsMeasureZero 𝓘(ℝ, Fin 2 → ℝ) K ↔ volume K = 0 := by
  refine ⟨fun h => ?_, fun h => isMeasureZero_of_forall_mem fun z _ =>
    ⟨chartAt (Fin 2 → ℝ) z, IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, Fin 2 → ℝ)) (n := ∞) z,
      mem_chart_source _ z, by rw [chartImage_chartAt_self]; exact h⟩⟩
  have h0 := h (chartAt (Fin 2 → ℝ) (0 : Fin 2 → ℝ))
    (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, Fin 2 → ℝ)) (n := ∞) 0)
  rwa [chartImage_chartAt_self] at h0

/-! #### Tame structures in `ℝⁿ` -/

section TrivialRn

variable {n : ℕ}

/-- In the trivial ep-groupoid of `ℝⁿ`, every local branching structure restricts to a tame one
(Definition 9.3.6): the domain of a natural representation inside `U(x)`, which has the
properness property; the sheets avoid `∂ℝⁿ = ∅`. -/
theorem exists_tameBranchingStructure_trivial_rn {Θ : (Fin n → ℝ) → ℚ} {x : Fin n → ℝ}
    (B : (trivial (rnPolyfold n)).LocalBranchingStructure Θ x) :
    ∃ T : (trivial (rnPolyfold n)).TameBranchingStructure Θ x, T.U ⊆ B.U ∧
      ∀ i, ∃ i₀, T.M i = B.M i₀ ∩ T.U := by
  obtain ⟨R, hR⟩ := theorem_7_1_13 (trivial (rnPolyfold n)) x B.isOpen_U B.mem_U
  let B' := B.restrict R.isOpen_U R.mem_U hR
  exact ⟨{ toLocalBranchingStructure := B'
           rep := R
           U_eq := rfl
           hasPropernessProperty := hasPropernessProperty_trivial (rnPolyfold n) R.isOpen_U
           hasTameInducedStructure := fun i =>
             MPolyfold.hasTameInducedStructure_of_degIndex_eq_zero (B'.isSmoothSubmanifold i)
               fun a _ => rnPolyfold_degIndex n a }, hR, fun i => ⟨i, rfl⟩⟩

/-- The standing assumption `HasTameSheetsIn` in `ℝⁿ`, for a class of sheets closed under
intersections with open sets. -/
theorem hasTameSheetsIn_trivial_rn {S : Set (Set (Fin n → ℝ))} {Θ : (Fin n → ℝ) → ℚ}
    (hSo : ∀ N ∈ S, ∀ V, IsOpen V → N ∩ V ∈ S)
    (h : ∀ x ∈ supp Θ, ∃ B : (trivial (rnPolyfold n)).LocalBranchingStructure Θ x,
      ∀ i, B.M i ∈ S) :
    (trivial (rnPolyfold n)).HasTameSheetsIn S Θ := fun x hx => by
  obtain ⟨B, hB⟩ := h x hx
  obtain ⟨T, -, hT⟩ := exists_tameBranchingStructure_trivial_rn B
  refine ⟨T, fun i => ?_⟩
  obtain ⟨i₀, e⟩ := hT i
  rw [e]
  exact hSo _ (hB i₀) _ T.isOpen_U

theorem injective_π_trivial_rn : Function.Injective (trivial (rnPolyfold n)).π := fun a b h => by
  obtain ⟨φ, h1, h2⟩ := (trivial (rnPolyfold n)).π_eq_π_iff.1 h
  exact h1.symm.trans h2

end TrivialRn

/-! #### Witness 1: Example 9.3.5 (graphs over the first axis of `ℝ²`) -/

section Example935

/-- **Satisfiability of `SheetMeasureGeometry`**: the graphs over the first axis of `ℝ²`
(`graphSheetGeometry`, null sets read in the chart `z ↦ z 0`); the null sets are local (`ℝ²` is
second countable), closed under countable unions, and the same for all graphs. -/
def graphSheetMeasureGeometry : (rnPolyfold 2).SheetMeasureGeometry graphSheets :=
  { graphSheetGeometry with
    isNull_iUnion := fun {N A} h => by
      change IsMeasureZero 𝓘(ℝ, ℝ) _
      rw [image_iUnion]
      exact isMeasureZero_iUnion h
    isNull_of_local := fun N _ A h => isMeasureZero_image_of_local _ h
    isNull_transfer := fun _ _ _ _ _ _ h => h }

/-- The null sets of the graphs over the first axis. -/
abbrev graphNull : SheetNullSets graphSheets := graphSheetMeasureGeometry.toSheetNullSets

open scoped Classical in
/-- **Example 9.3.5's `Θ`** (2021 p. 425): `Θ(y) = ♯{b | y ∈ G_b}` for the two graphs
`G⁺⁺, G⁻⁻` (`beta1`), touching at `0`. -/
def theta935 : (Fin 2 → ℝ) → ℚ := fun y => ∑ b with y ∈ graph2 (beta1 b), (1 : ℚ)

theorem isBranchedEpSubgroupoid_theta935 :
    (trivial (rnPolyfold 2)).IsBranchedEpSubgroupoid theta935 :=
  isBranchedEpSubgroupoid_sum_rn _ _ (fun _ => one_pos)
    (fun b => (rnPolyfold_isSubmanifoldOfDim_graph2 (contDiff_beta1 b)).1)
    (fun b => isClosed_graph2 (contDiff_beta1 b).continuous)

theorem hasTameSheetsIn_theta935 :
    (trivial (rnPolyfold 2)).HasTameSheetsIn graphSheets theta935 := by
  refine hasTameSheetsIn_trivial_rn ?_ fun x _ => ⟨localBranchingStructure_sum_rn _ _
    (fun _ => one_pos) (fun b => (rnPolyfold_isSubmanifoldOfDim_graph2 (contDiff_beta1 b)).1)
    (fun b => isClosed_graph2 (contDiff_beta1 b).continuous) x, fun i =>
      ⟨beta1 i.1, contDiff_beta1 _, _, (localBranchingStructure_sum_rn _ _ (fun _ => one_pos)
        (fun b => (rnPolyfold_isSubmanifoldOfDim_graph2 (contDiff_beta1 b)).1)
        (fun b => isClosed_graph2 (contDiff_beta1 b).continuous) x).isOpen_U, rfl⟩⟩
  rintro _ ⟨β, hβ, V, hV, rfl⟩ W hW
  exact ⟨β, hβ, V ∩ W, hV.inter hW, inter_assoc _ _ _⟩

theorem zero_mem_supp_theta935 : (0 : Fin 2 → ℝ) ∈ supp theta935 := by
  change 0 < theta935 0
  unfold theta935
  exact Finset.sum_pos (fun _ _ => one_pos) ⟨true, by simp [zero_mem_graph2_beta1]⟩

/-- **A nonempty set of measure zero (Definition 9.5.1)**: the point `|0|` of
`S = |supp(Θ)|`, where the two graphs of Example 9.3.5 touch. -/
theorem isMeasureZeroSupp_theta935_zero :
    (trivial (rnPolyfold 2)).IsMeasureZeroSupp graphNull theta935
      {(trivial (rnPolyfold 2)).π 0} := by
  intro x hx
  obtain ⟨T, hT⟩ := hasTameSheetsIn_theta935 x hx
  refine ⟨T, hT, fun i => ?_⟩
  change IsMeasureZero 𝓘(ℝ, ℝ) _
  refine isMeasureZero_of_subsingleton ?_
  rintro _ ⟨w, ⟨-, hw⟩, rfl⟩ _ ⟨w', ⟨-, hw'⟩, rfl⟩
  rw [injective_π_trivial_rn hw, injective_π_trivial_rn hw']

/-- **`S` does not have measure zero** for Example 9.3.5's `Θ`. -/
theorem not_isMeasureZeroSupp_theta935 :
    ¬ (trivial (rnPolyfold 2)).IsMeasureZeroSupp graphNull theta935
      ((trivial (rnPolyfold 2)).orbitSupp theta935) :=
  not_isMeasureZeroSupp_orbitSupp graphNull isBranchedEpSubgroupoid_theta935.isFunctorial
    ⟨0, zero_mem_supp_theta935⟩

/-- **Definition 9.5.3 is not trivial for Example 9.3.5's `Θ`**: `L(S)` contains `S` and the
nonempty null set `{|0|}`, and `S` is not of measure zero. -/
theorem lebesgueSigma_theta935 :
    ∃ K : Set ((trivial (rnPolyfold 2)).orbitSupp theta935), K.Nonempty ∧
      K ∈ (trivial (rnPolyfold 2)).measureZeroSets graphNull theta935 ∧
      MeasurableSet[(trivial (rnPolyfold 2)).lebesgueSigma graphNull theta935] K ∧
      univ ∉ (trivial (rnPolyfold 2)).measureZeroSets graphNull theta935 ∧
      MeasurableSet[(trivial (rnPolyfold 2)).lebesgueSigma graphNull theta935] univ := by
  set X := trivial (rnPolyfold 2)
  have h0 : X.π 0 ∈ X.orbitSupp theta935 := ⟨0, zero_mem_supp_theta935, rfl⟩
  have hK : Subtype.val '' ({⟨X.π 0, h0⟩} : Set (X.orbitSupp theta935)) = {X.π 0} := by
    rw [image_singleton]
  refine ⟨{⟨X.π 0, h0⟩}, singleton_nonempty _, ?_, ?_, fun h => ?_,
    @MeasurableSet.univ _ (X.lebesgueSigma graphNull theta935)⟩
  · change X.IsMeasureZeroSupp graphNull theta935 _
    rw [hK]; exact isMeasureZeroSupp_theta935_zero
  · refine measurableSet_lebesgueSigma_of_isMeasureZeroSupp graphNull ?_
    rw [hK]; exact isMeasureZeroSupp_theta935_zero
  · change X.IsMeasureZeroSupp graphNull theta935 _ at h
    rw [image_univ, Subtype.range_coe] at h
    exact not_isMeasureZeroSupp_theta935 h

end Example935

/-! #### Witness 2: the plane, a null set which is not Borel -/

section Plane

/-- The open subsets of `ℝ²`, the sheets of the `2`-dimensional `Θ = 1`. -/
def planeSheets : Set (Set (Fin 2 → ℝ)) := {N | IsOpen N}

/-- **Satisfiability of `SheetNullSets` in dimension `2`**: the open subsets of `ℝ²` with the null
sets of Definition 9.4.5 (Lebesgue measure zero). -/
def planeNull : SheetNullSets planeSheets where
  IsNull _ A := IsMeasureZero 𝓘(ℝ, Fin 2 → ℝ) A
  isNull_empty _ := isMeasureZero_empty
  isNull_mono h hA := h.mono hA
  isNull_iUnion h := isMeasureZero_iUnion h
  isNull_of_local _ _ A h := by
    simpa using isMeasureZero_image_of_local (I := 𝓘(ℝ, Fin 2 → ℝ)) id (A := A)
      (by simpa using h)
  isNull_transfer _ _ _ _ _ _ h := h
  not_isNull_self N hN hne h :=
    (IsOpen.measure_pos volume (show IsOpen N from hN) hne).ne' (isMeasureZero_rn2_iff.1 h)

/-- The single sheet `ℝ²` of `thetaPlane`. -/
def planeSheet : Unit → Set (Fin 2 → ℝ) := fun _ => univ

open scoped Classical in
/-- `Θ = 1` on `ℝ²` (one sheet `ℝ²`, weight `1`). -/
def thetaPlane : (Fin 2 → ℝ) → ℚ := fun y => ∑ i with y ∈ planeSheet i, (1 : ℚ)

theorem isSmoothSubmanifold_univ_rn2 : (rnPolyfold 2).IsSmoothSubmanifold univ := by
  simpa using rnPolyfold_isSmoothSubmanifold_range (n := 2) (s := id) contDiff_id fun _ => rfl

theorem isBranchedEpSubgroupoid_thetaPlane :
    (trivial (rnPolyfold 2)).IsBranchedEpSubgroupoid thetaPlane :=
  isBranchedEpSubgroupoid_sum_rn planeSheet _ (fun _ => one_pos)
    (fun _ => isSmoothSubmanifold_univ_rn2) fun _ => isClosed_univ

theorem mem_supp_thetaPlane (y : Fin 2 → ℝ) : y ∈ supp thetaPlane := by
  change 0 < thetaPlane y
  simp [thetaPlane, planeSheet]

theorem hasTameSheetsIn_thetaPlane :
    (trivial (rnPolyfold 2)).HasTameSheetsIn planeSheets thetaPlane :=
  hasTameSheetsIn_trivial_rn (fun N hN _ hV => IsOpen.inter (show IsOpen N from hN) hV)
    fun x _ => ⟨localBranchingStructure_sum_rn planeSheet _ (fun _ => one_pos)
      (fun _ => isSmoothSubmanifold_univ_rn2) (fun _ => isClosed_univ) x,
      fun _ => isOpen_univ.inter (localBranchingStructure_sum_rn planeSheet _ (fun _ => one_pos)
        (fun _ => isSmoothSubmanifold_univ_rn2) (fun _ => isClosed_univ) x).isOpen_U⟩

/-- **A member of `L(S)` that is not a Borel set** (Definition 9.5.3), for `Θ = 1` on `ℝ²`: the
`2^𝔠` subsets of the image of the axis `ℝ × 0` all have measure zero, while `S ≅ ℝ²` has at
most `𝔠` Borel sets. -/
theorem exists_mem_lebesgueSigma_not_borel_thetaPlane :
    ∃ K : Set ((trivial (rnPolyfold 2)).orbitSupp thetaPlane),
      K ∈ (trivial (rnPolyfold 2)).measureZeroSets planeNull thetaPlane ∧
      MeasurableSet[(trivial (rnPolyfold 2)).lebesgueSigma planeNull thetaPlane] K ∧
      ¬ MeasurableSet[borel _] K := by
  set X := trivial (rnPolyfold 2)
  have : SecondCountableTopology X.OrbitSpace :=
    (trivialOrbitHomeomorph (rnPolyfold 2)).secondCountableTopology
  have hcard : #{t : Set (X.orbitSupp thetaPlane) | MeasurableSet[borel _] t} ≤ 𝔠 := by
    rw [(TopologicalSpace.isBasis_countableBasis _).borel_eq_generateFrom]
    exact MeasurableSpace.cardinal_measurableSet_le_continuum
      ((Cardinal.mk_le_aleph0_iff.2
        (TopologicalSpace.countable_countableBasis _).to_subtype).trans
        Cardinal.aleph0_le_continuum)
  have hS : ∀ s : ℝ, X.π ![s, 0] ∈ X.orbitSupp thetaPlane := fun s =>
    ⟨_, mem_supp_thetaPlane _, rfl⟩
  let F : Set ℝ → Set (X.orbitSupp thetaPlane) := fun T => {p | ∃ s ∈ T, p.1 = X.π ![s, 0]}
  have hFinj : Function.Injective F := by
    intro T T' h
    ext s
    have key : ∀ {T T'}, F T = F T' → s ∈ T → s ∈ T' := fun {T T'} h hs => by
      have hm : (⟨X.π ![s, 0], hS s⟩ : X.orbitSupp thetaPlane) ∈ F T' := h ▸ ⟨s, hs, rfl⟩
      obtain ⟨s', hs', he⟩ := hm
      have := congrFun (injective_π_trivial_rn he) 0
      simp only [Matrix.cons_val_zero] at this
      rwa [this]
    exact ⟨key h, key h.symm⟩
  have hFnull : ∀ T, F T ∈ X.measureZeroSets planeNull thetaPlane := by
    intro T x hx
    obtain ⟨B, hB⟩ := hasTameSheetsIn_thetaPlane x hx
    refine ⟨B, hB, fun i => ?_⟩
    change IsMeasureZero 𝓘(ℝ, Fin 2 → ℝ) _
    refine IsMeasureZero.mono (isMeasureZero_rn2_iff.2
      (Measure.addHaar_submodule volume lineH lineH_ne_top)) ?_
    rintro w ⟨-, ⟨p, ⟨s, -, hps⟩, hpw⟩⟩
    rw [SetLike.mem_coe, mem_lineH, injective_π_trivial_rn (hpw.symm.trans hps)]
    rfl
  by_contra hcon
  push Not at hcon
  have hle : #(Set ℝ) ≤ #{t : Set (X.orbitSupp thetaPlane) | MeasurableSet[borel _] t} :=
    Cardinal.mk_le_of_injective (f := fun T => ⟨F T, hcon _ (hFnull T)
      (measurableSet_borelNullSigma_of_mem (hFnull T))⟩)
      fun T T' h => hFinj (congrArg Subtype.val h)
  have hlt : 𝔠 < #(Set ℝ) := by
    rw [Cardinal.mk_set, Cardinal.mk_real]
    exact Cardinal.cantor 𝔠
  exact absurd (hle.trans hcard) (not_le.2 hlt)

end Plane

/-! #### The transfer property across dimensions -/

/-- **The transfer field of `SheetNullSets` needs one dimension**: the axis `ℝ × 0` has measure
zero in the `2`-dimensional sheet `ℝ²` (Definition 9.4.5), but not in itself, a `1`-dimensional
sheet (in the chart `z ↦ z 0`); so no `SheetNullSets` contains both the planar null sets and the
null sets of graphs. -/
theorem isNull_transfer_mixed_dim :
    planeNull.IsNull univ axis2 ∧ ¬ graphNull.IsNull axis2 axis2 := by
  refine ⟨isMeasureZero_rn2_iff.2 ?_, graphNull.not_isNull_self axis2
    ⟨0, contDiff_const, univ, isOpen_univ, (inter_univ _).symm⟩ ⟨0, zero_mem_axis2⟩⟩
  refine measure_mono_null (fun v hv => ?_) (Measure.addHaar_submodule volume lineH lineH_ne_top)
  change v 1 = (0 : ℝ → ℝ) (v 0) at hv
  exact (mem_lineH).2 hv

end Witnesses

end Polyfold
