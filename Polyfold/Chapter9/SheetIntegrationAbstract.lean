import Polyfold.Chapter9.Measure
import Polyfold.Chapter11.BranchedEquivalenceTangent

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5 "Integration and Stokes": the integrals `∫_K ω|(M, o)` of an
sc-differential `n`-form over measurable subsets of oriented sheets, as they enter **Lemma 9.5.7**
(p. 439; 2017: Lemma 9.17, p. 324) and (9.20).  Numbers and pages are the 2021 text's.

# Integration over oriented sheets, and the independence of the branching structure

## The text, paraphrased

(p. 438) For an oriented local branching structure `(Mᵢ, oᵢ)`, `(σᵢ)` on `U(x)` and a measurable
`K ⊆ |M_U|` with preimages `Kᵢ ⊆ Mᵢ`, the local measures are weighted sums of the integrals
`∫_{Kᵢ} ω|(Mᵢ, oᵢ)`.  (Lemma 9.5.7, (9.20)) Two oriented structures on `U(x)` with the same
weighted sums (9.19) of oriented tangent spaces give the same sum `∑ σᵢ ∫_{Kᵢ} ω|(Mᵢ, oᵢ)`; the
proof removes a set of measure zero and compares the two sums on the pieces of Proposition 9.4.10,
on which the sheets through a point have one tangent space and two classes of orientations.

## What is formalized

* `SheetNullSets.sheetSigma`, `SheetNullSets.IsMeasIn`: the measurable subsets of a sheet `N`
  (Borel sets modified by null sets of `N`), with `IsMeasIn.transfer` (two sheets induce the same
  measurable subsets of their intersection).
* `EpGroupoid.SheetIntegration G Ω`: the integrals `integ ω N T_•(N, o) A = ∫_A ω|(N, o)` of the
  forms `ω ∈ Ω` over measurable subsets `A` of the oriented sheets `N ∈ S`, with the properties the
  text uses: linearity in `ω`, countable additivity (`integ_hasSum`), null sets (`integ_null`),
  the comparison of two sheets on a common subset where their oriented tangent spaces agree
  (`integ_congr`) or are opposite (`integ_neg`), invariance under the sc-diffeomorphisms whose
  tangent maps are the `Tψ` of morphisms (`integ_image`: `(Tψ)^*ω = ω`, Definition 8.2.1, and the
  change of variables), and three properties of the sheets (`lindelof`, `isMeasIn_inter`,
  `isNull_tangent_ne`: Lemma 9.4.6; `isMeasIn_tangent_eq`).
* **(9.20), Lemma 9.5.7** in the form used throughout: `sum_integ_eq_zero` (a finite family of
  oriented sheets with rational weights whose weighted sum of oriented tangent spaces vanishes at
  every point of `K` has `∑ w_k ∫_{K ∩ N_k} ω|(N_k, o_k) = 0`) and `sum_integ_eq_sum_integ` (two
  families with the same sums).  The families need not pass through one point.

## The choices made

* The sc-differential forms on ep-groupoids (Definition 8.2.1, gap G.74) and the integral of a form
  over a measurable subset of an oriented submanifold of an M-polyfold are not available in the
  repository.  As for the null sets of §9.5 (`SheetNullSets`) and the essential points of §9.4
  (`MPolyfold.SheetGeometry`), they are the data of a structure, `SheetIntegration`; the forms are
  the elements of a real vector space `Ω`, seen through their integrals.  A witness is in
  `PointIntegration.lean` (dimension `0`: the sheets are points, the integral is the
  signed value of an invariant function).  (2026-11-13) For the sc-forms of Definitions 8.2.1,
  8.2.2 and `n ≥ 1` the integral is constructed as a `SheetIntegration` in
  `SheetIntegrationConcrete.lean` (sheets in one graph chart) and
  `MultiChartIntegration.lean` (sheets covered by countably many graph charts).
* The proof of (9.20) follows the text's, with the decomposition of Proposition 9.4.10 redone for
  measurable pieces: after removing the points where two sheets through a point have different
  tangent spaces (a null set in every sheet), `K` is cut into the finitely many pieces on which
  the set of sheets through `y` and the pairs of sheets with equal oriented tangent space are
  constant; on a piece, the integrals over the sheets through it are `±` the integral over one of
  them, and the signed sum of the weights vanishes because a tangent space has two orientations.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory
open scoped symmDiff

noncomputable section

namespace Polyfold

universe u

/-! ### Measurable subsets of a sheet -/

namespace SheetNullSets

variable {X : Type u} [TopologicalSpace X] {S : Set (Set X)} (G : SheetNullSets S)

omit [TopologicalSpace X] in
theorem compl_inter_symmDiff (A B N : Set X) : (Aᶜ ∩ N) ∆ (Bᶜ ∩ N) = (A ∩ N) ∆ (B ∩ N) := by
  ext y
  simp only [Set.mem_symmDiff, mem_inter_iff, mem_compl_iff]
  tauto

/-- **The σ-algebra of the sheet `N`**: the sets `A` whose trace `A ∩ N` differs from the trace of
a Borel set by a null set of `N` (the Lebesgue measurable subsets of `N`, for the null sets of
Definition 9.4.5). -/
@[instance_reducible] def sheetSigma (N : Set X) : MeasurableSpace X where
  MeasurableSet' A := ∃ B, MeasurableSet[borel X] B ∧ G.IsNull N ((A ∩ N) ∆ (B ∩ N))
  measurableSet_empty := ⟨∅, MeasurableSpace.measurableSet_empty _, by
    rw [symmDiff_self]; exact G.isNull_empty N⟩
  measurableSet_compl := fun A ⟨B, hB, h⟩ =>
    ⟨Bᶜ, hB.compl, by rw [compl_inter_symmDiff]; exact h⟩
  measurableSet_iUnion := fun A hA => by
    choose B hB h using hA
    refine ⟨⋃ k, B k, MeasurableSet.iUnion hB, G.isNull_mono (G.isNull_iUnion h) ?_⟩
    rw [iUnion_inter, iUnion_inter]
    exact symmDiff_iUnion_subset _ _

/-- `A` (through its trace `A ∩ N`) is a measurable subset of the sheet `N`. -/
def IsMeasIn (N A : Set X) : Prop := MeasurableSet[G.sheetSigma N] A

variable {G}

theorem isMeasIn_iff {N A : Set X} :
    G.IsMeasIn N A ↔ ∃ B, MeasurableSet[borel X] B ∧ G.IsNull N ((A ∩ N) ∆ (B ∩ N)) := Iff.rfl

theorem isMeasIn_of_isNull {N A : Set X} (hA : G.IsNull N (A ∩ N)) : G.IsMeasIn N A :=
  ⟨∅, MeasurableSpace.measurableSet_empty _, by
    rw [empty_inter, show (A ∩ N) ∆ (∅ : Set X) = A ∩ N from symmDiff_bot _]; exact hA⟩

theorem isMeasIn_of_borel {N B : Set X} (hB : MeasurableSet[borel X] B) : G.IsMeasIn N B :=
  ⟨B, hB, by rw [symmDiff_self]; exact G.isNull_empty N⟩

theorem isMeasIn_inter_iff {N A : Set X} : G.IsMeasIn N (A ∩ N) ↔ G.IsMeasIn N A := by
  rw [isMeasIn_iff, isMeasIn_iff, inter_assoc, inter_self]

theorem isMeasIn_self (N : Set X) : G.IsMeasIn N N :=
  ⟨univ, MeasurableSet.univ, by
    rw [inter_self, univ_inter, symmDiff_self]; exact G.isNull_empty N⟩

theorem IsMeasIn.congr_inter {N A A' : Set X} (h : G.IsMeasIn N A) (hAA' : A ∩ N = A' ∩ N) :
    G.IsMeasIn N A' := by
  rw [← isMeasIn_inter_iff, ← hAA', isMeasIn_inter_iff]; exact h

/-- **Two sheets induce the same measurable subsets of their intersection**: if `N ∩ N'` is
measurable in `N'`, a subset `A ⊆ N ∩ N'` measurable in `N` is measurable in `N'`. -/
theorem IsMeasIn.transfer {N N' A : Set X} (hN : N ∈ S) (hN' : N' ∈ S)
    (hI : G.IsMeasIn N' (N ∩ N')) (hA : A ⊆ N ∩ N') (h : G.IsMeasIn N A) : G.IsMeasIn N' A := by
  obtain ⟨B, hB, hnull⟩ := h
  obtain ⟨C, hC, hnullC⟩ := hI
  refine ⟨B ∩ C, hB.inter hC, ?_⟩
  have h1 : G.IsNull N' (((A ∩ N) ∆ (B ∩ N)) ∩ (N ∩ N')) :=
    G.isNull_transfer N hN N' hN' _ inter_subset_right
      (G.isNull_mono hnull inter_subset_left)
  refine G.isNull_mono (G.isNull_union h1 hnullC) ?_
  intro y hy
  rw [Set.mem_symmDiff] at hy
  simp only [mem_union, Set.mem_symmDiff, mem_inter_iff]
  rcases hy with ⟨⟨hyA, hyN'⟩, hn⟩ | ⟨⟨⟨hyB, hyC⟩, hyN'⟩, hn⟩
  · have hyN : y ∈ N := (hA hyA).1
    by_cases hyB : y ∈ B
    · refine Or.inr (Or.inl ⟨⟨⟨hyN, hyN'⟩, hyN'⟩, fun hc => hn ⟨⟨hyB, hc.1⟩, hyN'⟩⟩)
    · exact Or.inl ⟨Or.inl ⟨⟨hyA, hyN⟩, fun hc => hyB hc.1⟩, hyN, hyN'⟩
  · by_cases hyN : y ∈ N
    · exact Or.inl ⟨Or.inr ⟨⟨hyB, hyN⟩, fun hc => hn ⟨hc.1, hyN'⟩⟩, hyN, hyN'⟩
    · exact Or.inr (Or.inr ⟨⟨hyC, hyN'⟩, fun hc => hyN hc.1.1⟩)

end SheetNullSets

/-! ### The integrals over oriented sheets -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

variable (X : EpGroupoid Obj Mor) in
/-- **The tangent map of the sc-diffeomorphism `f` is, at the points of `N`, the tangent map `Tψ`
of a morphism `ψ : w → f(w)`** (Definition 7.1.6): this holds for the local sc-diffeomorphisms
`t ∘ (s|U(φ))⁻¹` of the morphisms and for the maps `ϕ_g` of a natural representation.  An
sc-differential form `ω` of the ep-groupoid satisfies `(Tψ)^*ω = ω` (Definition 8.2.1), hence
`f^*ω = ω` along `N`. -/
def IsMorTangentOn {f f' : Obj → Obj} {U U' : Set Obj}
    (hf : X.PObj.IsScDiffeoOn X.PObj f f' U U') (N : Set Obj) : Prop :=
  ∀ w ∈ N, ∃ ψ : Mor, X.src ψ = w ∧ X.tgt ψ = f w ∧ ∀ α : X.PObj.TangentSpace,
    X.PObj.levelVal 1 (X.PObj.tangentProj α) = w →
      X.tangentMor ψ α = MPolyfold.tangentMapOn hf.isScSmoothOn α

variable (X : EpGroupoid Obj Mor) in
/-- **Integration of forms over the oriented sheets of a class `S`** (2021 §9.5, pp. 438–445):
for `ω` in a real vector space `Ω` of forms, a sheet `N ∈ S` with an orientation `o` and a
measurable `A ⊆ N`, the number `integ ω N T_•(N, o) A = ∫_A ω|(N, o)`; the orientation enters
through the field `y ↦ T_y(N, o)` of oriented tangent spaces.  The fields are the properties used
in the text: linearity; countable additivity on the measurable subsets of `N`; null sets have
integral `0`; on a common measurable subset of two sheets where the oriented tangent spaces agree
(are opposite) the integrals agree (are opposite); the integral is invariant under the
sc-diffeomorphisms whose tangent maps are those of morphisms (`IsMorTangentOn`), and the class
`S`, the measurable sets and the orientations are carried along; open pieces of sheets are
sheets; every sheet is hereditarily Lindelöf; `N ∩ N'` is measurable in `N`, and so is its subset where the oriented tangent spaces
agree; the set where the tangent spaces of two sheets differ is null (Lemma 9.4.6). -/
structure SheetIntegration {S : Set (Set Obj)} (G : SheetNullSets S) (Ω : Type*)
    [AddCommGroup Ω] [Module ℝ Ω] where
  /-- `∫_A ω|(N, o)`, with `g = T_•(N, o)`. -/
  integ : Ω → Set Obj → (Obj → X.PObj.OrTangent) → Set Obj → ℝ
  integ_add : ∀ ω τ N g A, integ (ω + τ) N g A = integ ω N g A + integ τ N g A
  integ_smul : ∀ (c : ℝ) ω N g A, integ (c • ω) N g A = c * integ ω N g A
  lindelof : ∀ N ∈ S, HereditarilyLindelofSpace N
  inter_mem : ∀ N ∈ S, ∀ V : Set Obj, IsOpen V → N ∩ V ∈ S
  isMeasIn_inter : ∀ N ∈ S, ∀ N' ∈ S, G.IsMeasIn N (N ∩ N')
  /-- Lemma 9.4.6 with the note of Definition 9.4.7. -/
  isNull_tangent_ne : ∀ N ∈ S, ∀ N' ∈ S, G.IsNull N
    {y | y ∈ N ∩ N' ∧ X.PObj.submanifoldTangent N y ≠ X.PObj.submanifoldTangent N' y}
  isMeasIn_tangent_eq : ∀ N ∈ S, ∀ N' ∈ S, ∀ {m m' : ℕ}
    (o : X.PObj.SubmanifoldOrientation N m) (o' : X.PObj.SubmanifoldOrientation N' m'),
    G.IsMeasIn N {y | y ∈ N ∩ N' ∧ o.tangent y = o'.tangent y}
  integ_hasSum : ∀ ω, ∀ N ∈ S, ∀ {m : ℕ} (o : X.PObj.SubmanifoldOrientation N m)
    (A : ℕ → Set Obj), (∀ k, A k ⊆ N) → (∀ k, G.IsMeasIn N (A k)) →
    Pairwise (Function.onFun Disjoint A) →
    HasSum (fun k => integ ω N o.tangent (A k)) (integ ω N o.tangent (⋃ k, A k))
  integ_null : ∀ ω, ∀ N ∈ S, ∀ {m : ℕ} (o : X.PObj.SubmanifoldOrientation N m) (A : Set Obj),
    A ⊆ N → G.IsNull N A → integ ω N o.tangent A = 0
  integ_congr : ∀ ω, ∀ N ∈ S, ∀ N' ∈ S, ∀ {m m' : ℕ}
    (o : X.PObj.SubmanifoldOrientation N m) (o' : X.PObj.SubmanifoldOrientation N' m')
    (A : Set Obj), A ⊆ N ∩ N' → G.IsMeasIn N A → (∀ y ∈ A, o.tangent y = o'.tangent y) →
    integ ω N o.tangent A = integ ω N' o'.tangent A
  integ_neg : ∀ ω, ∀ N ∈ S, ∀ N' ∈ S, ∀ {m m' : ℕ}
    (o : X.PObj.SubmanifoldOrientation N m) (o' : X.PObj.SubmanifoldOrientation N' m')
    (A : Set Obj), A ⊆ N ∩ N' → G.IsMeasIn N A →
    (∀ y ∈ A, X.PObj.submanifoldTangent N y = X.PObj.submanifoldTangent N' y ∧
      o.tangent y ≠ o'.tangent y) →
    integ ω N o.tangent A = -integ ω N' o'.tangent A
  image_mem : ∀ N ∈ S, ∀ {f f' : Obj → Obj} {U U' : Set Obj}
    (hf : X.PObj.IsScDiffeoOn X.PObj f f' U U'), N ⊆ U → X.IsMorTangentOn hf N → f '' N ∈ S
  isMeasIn_image : ∀ N ∈ S, ∀ {f f' : Obj → Obj} {U U' : Set Obj}
    (hf : X.PObj.IsScDiffeoOn X.PObj f f' U U'), N ⊆ U → X.IsMorTangentOn hf N →
    ∀ A, A ⊆ N → G.IsMeasIn N A → G.IsMeasIn (f '' N) (f '' A)
  /-- `f^*ω = ω` and the change of variables. -/
  integ_image : ∀ ω, ∀ N ∈ S, ∀ {m : ℕ} (o : X.PObj.SubmanifoldOrientation N m)
    (hM : X.PObj.IsSmoothSubmanifold N) {f f' : Obj → Obj} {U U' : Set Obj}
    (hf : X.PObj.IsScDiffeoOn X.PObj f f' U U') (hNU : N ⊆ U), X.IsMorTangentOn hf N →
    ∀ A, A ⊆ N → G.IsMeasIn N A →
    integ ω (f '' N) (o.mapDiffeo hM hf hNU).tangent (f '' A) = integ ω N o.tangent A

namespace SheetIntegration

variable {X : EpGroupoid Obj Mor} {S : Set (Set Obj)} {G : SheetNullSets S} {Ω : Type*}
  [AddCommGroup Ω] [Module ℝ Ω] (𝓘 : X.SheetIntegration G Ω)

section Additivity

variable (ω : Ω) {N : Set Obj} (hN : N ∈ S) {m : ℕ} (o : X.PObj.SubmanifoldOrientation N m)

include hN

theorem integ_empty : 𝓘.integ ω N o.tangent ∅ = 0 :=
  𝓘.integ_null ω N hN o ∅ (empty_subset _) (G.isNull_empty N)

omit hN in
theorem integ_zero_form (A : Set Obj) : 𝓘.integ (0 : Ω) N o.tangent A = 0 := by
  have h := 𝓘.integ_smul 0 (0 : Ω) N o.tangent A
  rwa [zero_smul, zero_mul] at h

/-- Additivity on two disjoint measurable subsets of a sheet. -/
theorem integ_union {A B : Set Obj} (hA : A ⊆ N) (hB : B ⊆ N) (hAm : G.IsMeasIn N A)
    (hBm : G.IsMeasIn N B) (hAB : Disjoint A B) :
    𝓘.integ ω N o.tangent (A ∪ B) = 𝓘.integ ω N o.tangent A + 𝓘.integ ω N o.tangent B := by
  classical
  set F : ℕ → Set Obj := fun k => if k = 0 then A else if k = 1 then B else ∅ with hF
  have hF0 : F 0 = A := by simp [hF]
  have hF1 : F 1 = B := by simp [hF]
  have hFk : ∀ k, k ∉ ({0, 1} : Finset ℕ) → F k = ∅ := fun k hk => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    simp [hF, hk.1, hk.2]
  have hsub : ∀ k, F k ⊆ N := fun k => by
    simp only [hF]; split_ifs <;> [exact hA; exact hB; exact empty_subset _]
  have hmeas : ∀ k, G.IsMeasIn N (F k) := fun k => by
    simp only [hF]; split_ifs <;> [exact hAm; exact hBm; exact MeasurableSpace.measurableSet_empty _]
  have hdisj : Pairwise (Function.onFun Disjoint F) := by
    intro i j hij
    simp only [Function.onFun, hF]
    split_ifs with h1 h2 h3 h4 h5 <;> simp_all [disjoint_comm]
  have hU : ⋃ k, F k = A ∪ B := by
    ext y
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨k, hk⟩
      simp only [hF] at hk
      split_ifs at hk <;> [exact Or.inl hk; exact Or.inr hk; exact hk.elim]
    · rintro (h | h)
      · exact ⟨0, hF0 ▸ h⟩
      · exact ⟨1, hF1 ▸ h⟩
  have h1 := 𝓘.integ_hasSum ω N hN o F hsub hmeas hdisj
  have h2 : HasSum (fun k => 𝓘.integ ω N o.tangent (F k))
      (∑ k ∈ ({0, 1} : Finset ℕ), 𝓘.integ ω N o.tangent (F k)) :=
    hasSum_sum_of_ne_finset_zero fun k hk => by rw [hFk k hk]; exact 𝓘.integ_empty ω hN o
  rw [hU] at h1
  rw [h1.unique h2, Finset.sum_pair (by norm_num), hF0, hF1]

/-- Additivity on a finite pairwise disjoint family of measurable subsets of a sheet. -/
theorem integ_biUnion_finset {T : Type*} (s : Finset T) (P : T → Set Obj) (hP : ∀ t, P t ⊆ N)
    (hPm : ∀ t, G.IsMeasIn N (P t)) (hd : Pairwise (Function.onFun Disjoint P)) :
    𝓘.integ ω N o.tangent (⋃ t ∈ s, P t) = ∑ t ∈ s, 𝓘.integ ω N o.tangent (P t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using 𝓘.integ_empty ω hN o
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha, ← ih]
    refine 𝓘.integ_union ω hN o (hP a) (iUnion₂_subset fun t _ => hP t) (hPm a)
      (s.measurableSet_biUnion fun t _ => hPm t) ?_
    refine disjoint_iUnion₂_right.2 fun t ht => hd fun h => ha (h ▸ ht)

/-- **Cutting a measurable set along a finite measurable partition, up to a null set.** -/
theorem integ_eq_sum_inter {T : Type*} [Fintype T] (P : T → Set Obj)
    (hPm : ∀ t, G.IsMeasIn N (P t)) (hd : Pairwise (Function.onFun Disjoint P)) {A : Set Obj}
    (hA : A ⊆ N) (hAm : G.IsMeasIn N A) (hnull : G.IsNull N (A \ ⋃ t, P t)) :
    𝓘.integ ω N o.tangent A = ∑ t, 𝓘.integ ω N o.tangent (A ∩ P t) := by
  have hsplit : A = (A \ ⋃ t, P t) ∪ ⋃ t ∈ (Finset.univ : Finset T), (A ∩ P t) := by
    ext y
    simp only [mem_union, Set.mem_sdiff, mem_iUnion, Finset.mem_univ, exists_true_left, mem_inter_iff,
      exists_and_left]
    tauto
  have hdm : G.IsMeasIn N (A \ ⋃ t, P t) := hAm.diff (MeasurableSet.iUnion hPm)
  have hum : G.IsMeasIn N (⋃ t ∈ (Finset.univ : Finset T), (A ∩ P t)) :=
    Finset.univ.measurableSet_biUnion fun t _ => hAm.inter (hPm t)
  have hd' : Pairwise (Function.onFun Disjoint fun t => A ∩ P t) := fun s t hst =>
    (hd hst).mono inter_subset_right inter_subset_right
  have h1 := 𝓘.integ_union ω hN o (A := A \ ⋃ t, P t)
    (B := ⋃ t ∈ (Finset.univ : Finset T), (A ∩ P t)) (sdiff_subset.trans hA)
    (iUnion₂_subset fun t _ => inter_subset_left.trans hA) hdm hum (by
      refine disjoint_iUnion₂_right.2 fun t _ => disjoint_left.2 fun y hy hy' => ?_
      exact hy.2 (mem_iUnion.2 ⟨t, hy'.2⟩))
  rw [← hsplit, 𝓘.integ_null ω N hN o _ (sdiff_subset.trans hA) hnull, zero_add,
    𝓘.integ_biUnion_finset ω hN o Finset.univ (fun t => A ∩ P t)
      (fun t => inter_subset_left.trans hA) (fun t => hAm.inter (hPm t)) hd'] at h1
  exact h1

end Additivity

include 𝓘 in
/-- A set measurable in every sheet of a countable family is measurable in every sheet `N'` whose
trace of the set is covered by the family. -/
theorem isMeasIn_of_cover {κ : Type*} [Countable κ] {N : κ → Set Obj} (hS : ∀ k, N k ∈ S)
    {N' : Set Obj} (hN' : N' ∈ S) {A : Set Obj} (hcov : A ∩ N' ⊆ ⋃ k, N k)
    (hA : ∀ k, G.IsMeasIn (N k) A) : G.IsMeasIn N' A := by
  have h : ∀ k, G.IsMeasIn N' (A ∩ (N k ∩ N')) := fun k =>
    SheetNullSets.IsMeasIn.transfer (hS k) hN'
      (by rw [inter_comm]; exact 𝓘.isMeasIn_inter _ hN' _ (hS k)) inter_subset_right
      ((hA k).inter (𝓘.isMeasIn_inter _ (hS k) _ hN'))
  refine SheetNullSets.IsMeasIn.congr_inter (MeasurableSet.iUnion h) ?_
  ext y
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨⟨k, hyA, -, -⟩, hyN'⟩
    exact ⟨hyA, hyN'⟩
  · rintro ⟨hyA, hyN'⟩
    obtain ⟨k, hk⟩ := mem_iUnion.1 (hcov ⟨hyA, hyN'⟩)
    exact ⟨⟨k, hyA, hk, hyN'⟩, hyN'⟩

/-! ### (9.20): families of oriented sheets with vanishing weighted sum -/

section Core

open scoped Classical

variable {κ : Type*} [Fintype κ] (N : κ → Set Obj) (m : κ → ℕ)
  (o : ∀ k, X.PObj.SubmanifoldOrientation (N k) (m k))

variable (X) in
/-- The points at which two sheets of the family have different tangent spaces. -/
def tangentBad : Set Obj :=
  {y | ∃ k l, y ∈ N k ∩ N l ∧
    X.PObj.submanifoldTangent (N k) y ≠ X.PObj.submanifoldTangent (N l) y}

/-- The points of `N_a ∩ N_b` at which the oriented tangent spaces agree. -/
def eqSet (a b : κ) : Set Obj := {y | y ∈ N a ∩ N b ∧ (o a).tangent y = (o b).tangent y}

/-- The type of a point: the sheets through it, and the pairs with equal oriented tangent
space. -/
def typeOf (y : Obj) : Finset κ × Finset (κ × κ) :=
  (Finset.univ.filter fun l => y ∈ N l, Finset.univ.filter fun p => y ∈ eqSet N m o p.1 p.2)

/-- The points of `K` of type `t` at which all sheets through the point have one tangent
space. -/
def piece (K : Set Obj) (t : Finset κ × Finset (κ × κ)) : Set Obj :=
  {y | y ∈ K ∧ y ∉ tangentBad X N ∧ typeOf N m o y = t}

variable {N m o}

include 𝓘 in
theorem isNull_tangentBad (hS : ∀ k, N k ∈ S) (k : κ) :
    G.IsNull (N k) (tangentBad X N ∩ N k) := by
  have h : ∀ l, G.IsNull (N k) {y | y ∈ N k ∩ N l ∧
      X.PObj.submanifoldTangent (N k) y ≠ X.PObj.submanifoldTangent (N l) y} := fun l =>
    𝓘.isNull_tangent_ne _ (hS k) _ (hS l)
  have : Finite κ := Finite.of_fintype κ
  refine G.isNull_mono (G.isNull_iUnion_countable h) ?_
  rintro y ⟨⟨a, b, ⟨hya, hyb⟩, hab⟩, hyk⟩
  by_cases hka : X.PObj.submanifoldTangent (N k) y = X.PObj.submanifoldTangent (N a) y
  · exact mem_iUnion.2 ⟨b, ⟨hyk, hyb⟩, fun h => hab (hka.symm.trans h)⟩
  · exact mem_iUnion.2 ⟨a, ⟨hyk, hya⟩, hka⟩

omit [Fintype κ] in
include 𝓘 in
theorem isMeasIn_eqSet (hS : ∀ k, N k ∈ S) (k a b : κ) : G.IsMeasIn (N k) (eqSet N m o a b) := by
  have h1 : G.IsMeasIn (N a) (eqSet N m o a b) :=
    𝓘.isMeasIn_tangent_eq _ (hS a) _ (hS b) (o a) (o b)
  have h3 : G.IsMeasIn (N a) (eqSet N m o a b ∩ (N a ∩ N k)) :=
    h1.inter (𝓘.isMeasIn_inter _ (hS a) _ (hS k))
  have h4 : G.IsMeasIn (N k) (eqSet N m o a b ∩ (N a ∩ N k)) :=
    SheetNullSets.IsMeasIn.transfer (hS a) (hS k)
      (by rw [inter_comm]; exact 𝓘.isMeasIn_inter _ (hS k) _ (hS a)) inter_subset_right h3
  refine h4.congr_inter ?_
  ext y
  simp only [mem_inter_iff, eqSet, mem_ofPred_eq]
  tauto

include 𝓘 in
theorem isMeasIn_piece (hS : ∀ k, N k ∈ S) {K : Set Obj}
    (hK : ∀ k, G.IsMeasIn (N k) (K ∩ N k)) (k : κ) (t : Finset κ × Finset (κ × κ)) :
    G.IsMeasIn (N k) (piece N m o K t) := by
  have hiff : ∀ (A : Set Obj) (c : Prop), G.IsMeasIn (N k) A →
      G.IsMeasIn (N k) {y | y ∈ A ↔ c} := by
    intro A c hA
    by_cases hc : c
    · have : {y | y ∈ A ↔ c} = A := by ext y; simp [hc]
      rw [this]; exact hA
    · have : {y | y ∈ A ↔ c} = Aᶜ := by ext y; simp [hc]
      rw [this]; exact hA.compl
  have hKm : G.IsMeasIn (N k) K := SheetNullSets.isMeasIn_inter_iff.1 (hK k)
  have hbad : G.IsMeasIn (N k) (tangentBad X N) :=
    SheetNullSets.isMeasIn_of_isNull (𝓘.isNull_tangentBad hS k)
  have hNl : ∀ l, G.IsMeasIn (N k) (N l) := fun l =>
    SheetNullSets.isMeasIn_inter_iff.1 (by
      rw [inter_comm]; exact 𝓘.isMeasIn_inter _ (hS k) _ (hS l))
  have h1 : G.IsMeasIn (N k) (⋂ l, {y | y ∈ N l ↔ l ∈ t.1}) :=
    MeasurableSet.iInter fun l => hiff _ _ (hNl l)
  have h2 : G.IsMeasIn (N k) (⋂ p : κ × κ, {y | y ∈ eqSet N m o p.1 p.2 ↔ p ∈ t.2}) :=
    MeasurableSet.iInter fun p => hiff _ _ (𝓘.isMeasIn_eqSet hS k p.1 p.2)
  have heq : piece N m o K t = K ∩ (tangentBad X N)ᶜ ∩ (⋂ l, {y | y ∈ N l ↔ l ∈ t.1}) ∩
      ⋂ p : κ × κ, {y | y ∈ eqSet N m o p.1 p.2 ↔ p ∈ t.2} := by
    ext y
    simp only [piece, typeOf, mem_ofPred_eq, mem_inter_iff, mem_compl_iff, mem_iInter,
      Prod.ext_iff, Finset.ext_iff, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  rw [heq]
  exact ((hKm.inter hbad.compl).inter h1).inter h2

theorem pairwise_disjoint_piece (K : Set Obj) :
    Pairwise (Function.onFun Disjoint (piece N m o K)) := fun _ _ hst =>
  disjoint_left.2 fun _ hy hy' => hst (hy.2.2.symm.trans hy'.2.2)

theorem mem_piece_typeOf {K : Set Obj} {y : Obj} (hy : y ∈ K) (hb : y ∉ tangentBad X N) :
    y ∈ piece N m o K (typeOf N m o y) := ⟨hy, hb, rfl⟩

theorem mem_iff_of_mem_piece {K : Set Obj} {t : Finset κ × Finset (κ × κ)} {y : Obj}
    (hy : y ∈ piece N m o K t) (k : κ) : y ∈ N k ↔ k ∈ t.1 := by
  have h := hy.2.2
  rw [← h]
  simp [typeOf]

theorem tangent_eq_iff_of_mem_piece {K : Set Obj} {t : Finset κ × Finset (κ × κ)} {y : Obj}
    (hy : y ∈ piece N m o K t) {a b : κ} (ha : a ∈ t.1) (hb : b ∈ t.1) :
    (o a).tangent y = (o b).tangent y ↔ (a, b) ∈ t.2 := by
  have hya := (mem_iff_of_mem_piece hy a).2 ha
  have hyb := (mem_iff_of_mem_piece hy b).2 hb
  have h := hy.2.2
  rw [← h]
  simp [typeOf, eqSet, hya, hyb]

theorem carrier_eq_of_mem_piece {K : Set Obj} {t : Finset κ × Finset (κ × κ)} {y : Obj}
    (hy : y ∈ piece N m o K t) {a b : κ} (ha : a ∈ t.1) (hb : b ∈ t.1) :
    X.PObj.submanifoldTangent (N a) y = X.PObj.submanifoldTangent (N b) y := by
  by_contra h
  exact hy.2.1 ⟨a, b, ⟨(mem_iff_of_mem_piece hy a).2 ha, (mem_iff_of_mem_piece hy b).2 hb⟩, h⟩

/-- **The signed sum of the weights on a piece vanishes**: at a point `y` of a piece, with
`k₀` a sheet through `y`, `∑_{k ∋ y} ± w_k = 0`, the sign being `+` iff
`T_y(N_k, o_k) = T_y(N_{k₀}, o_{k₀})` (a tangent space has two orientations). -/
theorem sum_sign_weight_eq_zero {K : Set Obj} {t : Finset κ × Finset (κ × κ)} {y : Obj}
    (hy : y ∈ piece N m o K t) (w : κ → ℚ)
    (hsum : ∑ k, (if y ∈ N k then Finsupp.single ((o k).tangent y) (w k) else 0) = 0)
    {k₀ : κ} (hk₀ : k₀ ∈ t.1) :
    ∑ k ∈ t.1, w k * (if (k, k₀) ∈ t.2 then (1 : ℚ) else -1) = 0 := by
  have hF : ∀ g : X.PObj.OrTangent,
      ∑ k ∈ t.1, (if (o k).tangent y = g then w k else 0) = 0 := by
    intro g
    have h := congrArg (fun v : X.PObj.OrTangent →₀ ℚ => v g) hsum
    simp only [Finsupp.finsetSum_apply, Finsupp.coe_zero, Pi.zero_apply] at h
    refine Eq.trans ?_ h
    rw [← Finset.sum_subset (Finset.subset_univ t.1) fun k _ hk => by
      rw [if_neg fun h' => hk ((mem_iff_of_mem_piece hy k).1 h')]; rfl]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [if_pos ((mem_iff_of_mem_piece hy k).2 hk), Finsupp.single_apply]
  have hsplit : ∀ k ∈ t.1, w k * (if (k, k₀) ∈ t.2 then (1 : ℚ) else -1) =
      (if (o k).tangent y = (o k₀).tangent y then w k else 0) -
        (if (o k).tangent y = (o k₀).tangent y then 0 else w k) := by
    intro k hk
    by_cases hc : (k, k₀) ∈ t.2
    · rw [if_pos hc, if_pos ((tangent_eq_iff_of_mem_piece hy hk hk₀).2 hc),
        if_pos ((tangent_eq_iff_of_mem_piece hy hk hk₀).2 hc)]
      ring
    · rw [if_neg hc, if_neg fun h => hc ((tangent_eq_iff_of_mem_piece hy hk hk₀).1 h),
        if_neg fun h => hc ((tangent_eq_iff_of_mem_piece hy hk hk₀).1 h)]
      ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, hF, zero_sub, neg_eq_zero]
  by_cases hall : ∀ k ∈ t.1, (o k).tangent y = (o k₀).tangent y
  · exact Finset.sum_eq_zero fun k hk => if_pos (hall k hk)
  · push Not at hall
    obtain ⟨k₁, hk₁, hne⟩ := hall
    refine Eq.trans ?_ (hF ((o k₁).tangent y))
    refine Finset.sum_congr rfl fun k hk => ?_
    have hyk := (mem_iff_of_mem_piece hy k).2 hk
    have hyk₁ := (mem_iff_of_mem_piece hy k₁).2 hk₁
    have hyk₀ := (mem_iff_of_mem_piece hy k₀).2 hk₀
    by_cases hc : (o k).tangent y = (o k₀).tangent y
    · rw [if_pos hc, if_neg fun h => hne (h.symm.trans hc)]
    · rw [if_neg hc]
      rcases MPolyfold.OrTangent.eq_or_eq_or_eq_of_isOrientedAt
        ((o k).isOrientedAt_tangent hyk) ((o k₁).isOrientedAt_tangent hyk₁)
        ((o k₀).isOrientedAt_tangent hyk₀) (carrier_eq_of_mem_piece hy hk hk₁)
        (carrier_eq_of_mem_piece hy hk hk₀) with h | h | h
      · rw [if_pos h]
      · exact absurd h hc
      · exact absurd h hne

/-- **(9.20) for a family with vanishing weighted sum**: let `(N_k, o_k)` be finitely many
oriented sheets of the class `S` with weights `w_k ∈ ℚ`, and `K` a set whose traces `K ∩ N_k` are
measurable, such that `∑_{k, y ∈ N_k} w_k · T_y(N_k, o_k) = 0` at every `y ∈ K`.  Then
`∑_k w_k ∫_{K ∩ N_k} ω|(N_k, o_k) = 0`. -/
theorem sum_integ_eq_zero (ω : Ω) (hS : ∀ k, N k ∈ S) (w : κ → ℚ) {K : Set Obj}
    (hK : ∀ k, G.IsMeasIn (N k) (K ∩ N k))
    (hsum : ∀ y ∈ K,
      ∑ k, (if y ∈ N k then Finsupp.single ((o k).tangent y) (w k) else 0) = 0) :
    ∑ k, (w k : ℝ) * 𝓘.integ ω (N k) (o k).tangent (K ∩ N k) = 0 := by
  -- cut every `K ∩ N_k` into the pieces
  have hcut : ∀ k, 𝓘.integ ω (N k) (o k).tangent (K ∩ N k) =
      ∑ t, 𝓘.integ ω (N k) (o k).tangent (piece N m o K t ∩ N k) := by
    intro k
    rw [𝓘.integ_eq_sum_inter ω (hS k) (o k) (piece N m o K) (𝓘.isMeasIn_piece hS hK k)
      (pairwise_disjoint_piece K) inter_subset_right (hK k) ?_]
    · refine Finset.sum_congr rfl fun t _ => congrArg _ ?_
      ext y
      simp only [mem_inter_iff, piece, mem_ofPred_eq]
      tauto
    · refine G.isNull_mono (𝓘.isNull_tangentBad hS k) ?_
      rintro y ⟨⟨hyK, hyk⟩, hn⟩
      refine ⟨?_, hyk⟩
      by_contra hb
      exact hn (mem_iUnion.2 ⟨_, mem_piece_typeOf hyK hb⟩)
  simp_rw [hcut, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun t _ => ?_
  -- one piece
  set Q := piece N m o K t with hQ
  have hint : ∀ k, Q ∩ N k = if k ∈ t.1 then Q else ∅ := by
    intro k
    split_ifs with hk
    · exact inter_eq_left.2 fun y hy => (mem_iff_of_mem_piece hy k).2 hk
    · exact eq_empty_of_forall_notMem fun y hy => hk ((mem_iff_of_mem_piece hy.1 k).1 hy.2)
  by_cases hne : Q.Nonempty
  swap
  · refine Finset.sum_eq_zero fun k _ => ?_
    rw [not_nonempty_iff_eq_empty.1 hne, empty_inter, 𝓘.integ_empty ω (hS k) (o k), mul_zero]
  obtain ⟨y₀, hy₀⟩ := hne
  have hterm : ∀ k, (w k : ℝ) * 𝓘.integ ω (N k) (o k).tangent (Q ∩ N k) =
      if k ∈ t.1 then (w k : ℝ) * 𝓘.integ ω (N k) (o k).tangent Q else 0 := by
    intro k
    rw [hint k]
    split_ifs
    · rfl
    · rw [𝓘.integ_empty ω (hS k) (o k), mul_zero]
  simp_rw [hterm]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  rcases t.1.eq_empty_or_nonempty with he | ⟨k₀, hk₀⟩
  · rw [he, Finset.sum_empty]
  have hrel : ∀ k ∈ t.1, 𝓘.integ ω (N k) (o k).tangent Q =
      ((if (k, k₀) ∈ t.2 then (1 : ℚ) else -1 : ℚ) : ℝ) *
        𝓘.integ ω (N k₀) (o k₀).tangent Q := by
    intro k hk
    have hsub : Q ⊆ N k ∩ N k₀ := fun y hy =>
      ⟨(mem_iff_of_mem_piece hy k).2 hk, (mem_iff_of_mem_piece hy k₀).2 hk₀⟩
    have hm : G.IsMeasIn (N k) Q := 𝓘.isMeasIn_piece hS hK k t
    by_cases hc : (k, k₀) ∈ t.2
    · rw [if_pos hc, Rat.cast_one, one_mul]
      exact 𝓘.integ_congr ω _ (hS k) _ (hS k₀) (o k) (o k₀) Q hsub hm fun y hy =>
        (tangent_eq_iff_of_mem_piece hy hk hk₀).2 hc
    · rw [if_neg hc, Rat.cast_neg, Rat.cast_one, neg_one_mul]
      exact 𝓘.integ_neg ω _ (hS k) _ (hS k₀) (o k) (o k₀) Q hsub hm fun y hy =>
        ⟨carrier_eq_of_mem_piece hy hk hk₀,
          fun h => hc ((tangent_eq_iff_of_mem_piece hy hk hk₀).1 h)⟩
  rw [Finset.sum_congr rfl fun k hk => by rw [hrel k hk, ← mul_assoc], ← Finset.sum_mul]
  have h0 := sum_sign_weight_eq_zero hy₀ w (hsum y₀ hy₀.1) hk₀
  have h0' : ∑ k ∈ t.1, (w k : ℝ) * ((if (k, k₀) ∈ t.2 then (1 : ℚ) else -1 : ℚ) : ℝ) = 0 := by
    have := congrArg (fun q : ℚ => (q : ℝ)) h0
    simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_zero] using this
  rw [h0', zero_mul]

end Core

/-- **(9.20), Lemma 9.5.7 for two families of oriented sheets (2021 p. 440)**: let `(N_k, o_k)`,
`(w_k)` and `(N'_l, o'_l)`, `(w'_l)` be two finite families of oriented sheets of the class `S`
with rational weights, and `K` a set with measurable traces on all sheets such that the weighted
sums of oriented tangent spaces agree at every `y ∈ K`,
`∑_{y ∈ N_k} w_k · T_y(N_k, o_k) = ∑_{y ∈ N'_l} w'_l · T_y(N'_l, o'_l)` (9.19).  Then
`∑_k w_k ∫_{K ∩ N_k} ω|(N_k, o_k) = ∑_l w'_l ∫_{K ∩ N'_l} ω|(N'_l, o'_l)`. -/
theorem sum_integ_eq_sum_integ (ω : Ω) {κ κ' : Type*} [Fintype κ] [Fintype κ']
    {N : κ → Set Obj} {m : κ → ℕ} (o : ∀ k, X.PObj.SubmanifoldOrientation (N k) (m k))
    {N' : κ' → Set Obj} {m' : κ' → ℕ} (o' : ∀ l, X.PObj.SubmanifoldOrientation (N' l) (m' l))
    (hS : ∀ k, N k ∈ S) (hS' : ∀ l, N' l ∈ S) (w : κ → ℚ) (w' : κ' → ℚ) {K : Set Obj}
    (hK : ∀ k, G.IsMeasIn (N k) (K ∩ N k)) (hK' : ∀ l, G.IsMeasIn (N' l) (K ∩ N' l))
    (hsum : ∀ y ∈ K, (open scoped Classical in
      ∑ k, (if y ∈ N k then Finsupp.single ((o k).tangent y) (w k) else 0)) =
      (open scoped Classical in
      ∑ l, (if y ∈ N' l then Finsupp.single ((o' l).tangent y) (w' l) else 0))) :
    ∑ k, (w k : ℝ) * 𝓘.integ ω (N k) (o k).tangent (K ∩ N k) =
      ∑ l, (w' l : ℝ) * 𝓘.integ ω (N' l) (o' l).tangent (K ∩ N' l) := by
  classical
  let N'' : κ ⊕ κ' → Set Obj := Sum.elim N N'
  let m'' : κ ⊕ κ' → ℕ := Sum.elim m m'
  let o'' : ∀ s, X.PObj.SubmanifoldOrientation (N'' s) (m'' s) := fun s =>
    match s with
    | Sum.inl k => o k
    | Sum.inr l => o' l
  let w'' : κ ⊕ κ' → ℚ := Sum.elim w fun l => -w' l
  have h := 𝓘.sum_integ_eq_zero (N := N'') (m := m'') (o := o'') ω
    (by rintro (k | l); exacts [hS k, hS' l]) w'' (K := K)
    (by rintro (k | l); exacts [hK k, hK' l]) (fun y hy => by
      rw [Fintype.sum_sum_type]
      have e := hsum y hy
      change (∑ k, if y ∈ N k then Finsupp.single ((o k).tangent y) (w k) else 0) +
        (∑ l, if y ∈ N' l then Finsupp.single ((o' l).tangent y) (-w' l) else 0) = 0
      simp only [Finsupp.single_neg]
      have e2 : ∀ l, (if y ∈ N' l then -Finsupp.single ((o' l).tangent y) (w' l) else 0) =
          -(if y ∈ N' l then Finsupp.single ((o' l).tangent y) (w' l) else 0) := fun l => by
        split_ifs <;> simp
      simp only [e2, Finset.sum_neg_distrib]
      rw [add_neg_eq_zero]
      convert e)
  rw [Fintype.sum_sum_type] at h
  change (∑ k, (w k : ℝ) * 𝓘.integ ω (N k) (o k).tangent (K ∩ N k)) +
    (∑ l, ((-w' l : ℚ) : ℝ) * 𝓘.integ ω (N' l) (o' l).tangent (K ∩ N' l)) = 0 at h
  simp only [Rat.cast_neg, neg_mul, Finset.sum_neg_distrib] at h
  linarith

end SheetIntegration

end EpGroupoid

end Polyfold
