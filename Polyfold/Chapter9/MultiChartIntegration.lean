import Polyfold.Chapter9.MultiChart

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5 "Integration and Stokes", pp. 438–445 (gap G.107).  Numbers and pages
are the 2021 text's.

# The integration of forms over oriented sheets covered by several graph charts

For an evaluation of forms `F : X.FormEval n Ω` (`n ≥ 1`):

* `F.msInteg ω N T_•(N, o) A = ∫_A ω|(N, o)` for the sheets `N ∈ F.msheets` (countably many
  graph charts, `∫_N |ω| < ∞`, `MultiChart.lean`): the glued integral of any chart
  cover (`msInteg_eq`, independent of the cover);
* **`F.msheetIntegration hn : X.SheetIntegration F.msheetNull Ω`**: all fields of the structure of
  `SheetIntegrationAbstract.lean`, so that (9.20), Lemmas 9.5.7, 9.5.9–9.5.11 and Theorems
  9.5.4, 9.5.5 of `GapP2_E1_*.lean` apply to sheets which do not lie in one chart;
* `sheets_subset_msheets`, `msInteg_eq_integ`: the class contains E3's class `F.sheets`, and the
  integrals agree there.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {n : ℕ} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω] {F : X.FormEval n Ω}

namespace FormEval

variable {N N' : Set Obj}

theorem msheets_dim_eq (hN : N ∈ F.msheets) {m : ℕ} (o : X.PObj.SubmanifoldOrientation N m)
    {y : Obj} (hy : y ∈ N) : m = n := by
  obtain ⟨D, -⟩ := hN.2
  obtain ⟨k, hk⟩ := mem_iUnion.1 (D.cover hy)
  exact dim_eq (D.mem k) (o.restrict (D.isOpen k)) ⟨hy, hk⟩

/-- **The class of one-chart sheets lies in the class of several-chart sheets.** -/
theorem sheets_subset_msheets : F.sheets ⊆ F.msheets := fun _ hN =>
  ⟨hN.1, ChartCover.single F hN, ChartCover.single_isFinite hN⟩

theorem msheets_inter_isOpen (hN : N ∈ F.msheets) {W : Set Obj} (hW : IsOpen W) :
    N ∩ W ∈ F.msheets := by
  obtain ⟨D, hD⟩ := hN.2
  exact ⟨hN.1.inter_isOpen hW, D.restrict hW, D.restrict_isFinite hN.1.1 hD hW⟩

theorem msheets_image (hN : N ∈ F.msheets) {f f' : Obj → Obj} {U U' : Set Obj}
    (hf : X.PObj.IsScDiffeoOn X.PObj f f' U U') (hNU : N ⊆ U) (hmor : X.IsMorTangentOn hf N) :
    f '' N ∈ F.msheets := by
  obtain ⟨D, hD⟩ := hN.2
  exact ⟨hN.1.image_of_isScDiffeoOn hf hNU, D.image hf hNU hmor,
    D.image_isFinite hf hNU hmor hD⟩

namespace ChartCover

variable (D : F.ChartCover N)

theorem term_inter (ω : Ω) (o : X.PObj.SubmanifoldOrientation N n) (A : Set Obj) (k : ℕ) :
    D.term ω o (A ∩ N) k = D.term ω o A k := by
  unfold term
  rw [inter_assoc, inter_eq_right.2 fun y hy => (D.P_subset k hy).1]

theorem gInteg_inter (ω : Ω) (o : X.PObj.SubmanifoldOrientation N n) (A : Set Obj) :
    D.gInteg ω o (A ∩ N) = D.gInteg ω o A :=
  tsum_congr fun k => D.term_inter ω o A k

theorem isMeasIn_piece (hNb : MeasurableSet[borel Obj] N) {A : Set Obj}
    (hAm : F.sheetNull.IsMeasIn N A) (k : ℕ) {Q : Set Obj} (hQ : MeasurableSet[borel Obj] Q) :
    F.sheetNull.IsMeasIn (N ∩ D.V k) (A ∩ D.P k ∩ Q) :=
  isMeasIn_of_superset inter_subset_left
    (@MeasurableSet.inter Obj (F.sheetNull.sheetSigma N) _ _
      (@MeasurableSet.inter Obj (F.sheetNull.sheetSigma N) _ _ hAm
        (SheetNullSets.isMeasIn_of_borel (D.measurableSet_P hNb k)))
      (SheetNullSets.isMeasIn_of_borel hQ))

end ChartCover

open Classical in
variable (F) in
/-- **`∫_A ω|(N, o)` for a sheet covered by several graph charts**, `g = T_•(N, o)`: the glued
integral of the chosen chart cover (zero if `A` is not measurable in `N`). -/
def msInteg (ω : Ω) (N : Set Obj) (g : Obj → X.PObj.OrTangent) (A : Set Obj) : ℝ :=
  if h : (N ∈ F.msheets ∧ ∃ o : X.PObj.SubmanifoldOrientation N n, g = o.tangent) ∧
      F.sheetNull.IsMeasIn N A then
    h.1.1.2.choose.gInteg ω h.1.2.choose A
  else 0

/-- **The integral over a sheet of `F.msheets` is the glued integral of any finite chart
cover.** -/
theorem msInteg_eq (hn : 0 < n) (hN : N ∈ F.msheets) (D : F.ChartCover N) (hD : D.IsFinite)
    (o : X.PObj.SubmanifoldOrientation N n) (ω : Ω) {A : Set Obj}
    (hA : F.sheetNull.IsMeasIn N A) : F.msInteg ω N o.tangent A = D.gInteg ω o A := by
  have h : (N ∈ F.msheets ∧ ∃ o' : X.PObj.SubmanifoldOrientation N n, o.tangent = o'.tangent) ∧
      F.sheetNull.IsMeasIn N A := ⟨⟨hN, o, rfl⟩, hA⟩
  unfold msInteg
  rw [dif_pos h]
  have hNb := hN.1.1.measurableSet_borel
  have hto : o.tangent = h.1.2.choose.tangent := h.1.2.choose_spec
  have hAN : F.sheetNull.IsMeasIn N (A ∩ N) := SheetNullSets.isMeasIn_inter_iff.2 hA
  rw [← ChartCover.gInteg_inter, ← D.gInteg_inter]
  have e := h.1.1.2.choose.gInteg_eq_of hn D h.1.1.2.choose_spec hNb hNb ω h.1.2.choose o
    (A := A ∩ N) (fun y hy => ⟨hy.2, hy.2⟩) hAN 1 fun k l => by
      rw [one_mul]
      refine (F.sheetIntegration hn).integ_congr ω _ (h.1.1.2.choose.mem k) _ (D.mem l) _ _ _
        (fun y hy => ⟨h.1.1.2.choose.P_subset k hy.1.2, D.P_subset l hy.2⟩)
        (h.1.1.2.choose.isMeasIn_piece hNb hAN k (D.measurableSet_P hNb l)) fun y hy => ?_
      rw [MPolyfold.SubmanifoldOrientation.restrict_tangent _ _
          (h.1.1.2.choose.P_subset k hy.1.2).2,
        MPolyfold.SubmanifoldOrientation.restrict_tangent _ _ (D.P_subset l hy.2).2]
      exact (congrFun hto y).symm
  rw [e, one_mul]

/-- **The comparison of two sheets** through the pieces of finite chart covers. -/
theorem msInteg_rel (hn : 0 < n) (hN : N ∈ F.msheets) (hN' : N' ∈ F.msheets)
    (o : X.PObj.SubmanifoldOrientation N n) (o' : X.PObj.SubmanifoldOrientation N' n) (ω : Ω)
    {A : Set Obj} (hA : A ⊆ N ∩ N') (hAm : F.sheetNull.IsMeasIn N A) (s : ℝ)
    (hrel : ∀ (M M' : Set Obj), M ∈ F.sheets → M' ∈ F.sheets →
      ∀ (p : X.PObj.SubmanifoldOrientation M n) (p' : X.PObj.SubmanifoldOrientation M' n)
        (B : Set Obj), B ⊆ M ∩ M' → B ⊆ A → F.sheetNull.IsMeasIn M B →
        (∀ y ∈ B, p.tangent y = o.tangent y) → (∀ y ∈ B, p'.tangent y = o'.tangent y) →
        F.integ ω M p.tangent B = s * F.integ ω M' p'.tangent B) :
    F.msInteg ω N o.tangent A = s * F.msInteg ω N' o'.tangent A := by
  obtain ⟨D, hD⟩ := hN.2
  obtain ⟨D', hD'⟩ := hN'.2
  have hNb := hN.1.1.measurableSet_borel
  have hN'b := hN'.1.1.measurableSet_borel
  rw [msInteg_eq hn hN D hD o ω hAm, msInteg_eq hn hN' D' hD' o' ω (isMeasIn_transfer hNb hA hAm)]
  refine D.gInteg_eq_of hn D' hD hNb hN'b ω o o' hA hAm s fun k l => hrel _ _ (D.mem k)
    (D'.mem l) _ _ _ (fun y hy => ⟨D.P_subset k hy.1.2, D'.P_subset l hy.2⟩)
    (fun y hy => hy.1.1) (D.isMeasIn_piece hNb hAm k (D'.measurableSet_P hN'b l))
    (fun y hy => MPolyfold.SubmanifoldOrientation.restrict_tangent _ _ (D.P_subset k hy.1.2).2)
    (fun y hy => MPolyfold.SubmanifoldOrientation.restrict_tangent _ _ (D'.P_subset l hy.2).2)

theorem msInteg_of_inter_eq_empty (ω : Ω) (g : Obj → X.PObj.OrTangent) {A : Set Obj}
    (hA : A ∩ N = ∅) : F.msInteg ω N g A = 0 := by
  unfold msInteg
  split_ifs with h
  · unfold ChartCover.gInteg
    refine (tsum_congr fun k => ?_).trans tsum_zero
    refine integ_of_inter_eq_empty ω _ (eq_empty_of_forall_notMem fun y hy => ?_)
    have : y ∈ A ∩ N := ⟨hy.1.1, hy.1.2.1⟩
    rw [hA] at this
    exact this
  · rfl

theorem msheets_secondCountable (hN : N ∈ F.msheets) : SecondCountableTopology N := by
  obtain ⟨D, -⟩ := hN.2
  have hsc : ∀ k, SecondCountableTopology ↥(N ∩ D.V k) := fun k =>
    (coordHomeomorph (chart (D.mem k))).secondCountableTopology
  let U : ℕ → Set N := fun k => Subtype.val ⁻¹' D.V k
  have hU : ∀ k, SecondCountableTopology (U k) := fun k => by
    let e : U k → ↥(N ∩ D.V k) := fun y => ⟨y.1.1, y.1.2, y.2⟩
    have he : Topology.IsEmbedding e := by
      refine ⟨?_, fun a b h => ?_⟩
      · have h1 : Topology.IsInducing (fun y : U k => (y.1.1 : Obj)) :=
          Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
        have h2 : (fun y : U k => (y.1.1 : Obj)) = Subtype.val ∘ e := rfl
        rw [h2] at h1
        exact (Topology.IsInducing.of_comp_iff Topology.IsInducing.subtypeVal).1 h1
      · have h3 : (e a : Obj) = e b := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext h3)
    exact he.secondCountableTopology
  exact TopologicalSpace.secondCountableTopology_of_countable_cover
    (fun k => (D.isOpen k).preimage continuous_subtype_val)
    (eq_univ_of_forall fun y => by
      obtain ⟨k, hk⟩ := mem_iUnion.1 (D.cover y.2)
      exact mem_iUnion.2 ⟨k, hk⟩)

theorem msheets_isMeasIn_tangent_eq (hn : 0 < n) (hN : N ∈ F.msheets) (hN' : N' ∈ F.msheets)
    {m m' : ℕ} (o : X.PObj.SubmanifoldOrientation N m)
    (o' : X.PObj.SubmanifoldOrientation N' m') :
    F.sheetNull.IsMeasIn N {y | y ∈ N ∩ N' ∧ o.tangent y = o'.tangent y} := by
  obtain ⟨D, -⟩ := hN.2
  obtain ⟨D', -⟩ := hN'.2
  set E : ℕ → ℕ → Set Obj := fun k l => {y | y ∈ (N ∩ D.V k) ∩ (N' ∩ D'.V l) ∧
    (o.restrict (D.isOpen k)).tangent y = (o'.restrict (D'.isOpen l)).tangent y} with hE
  have hEm : ∀ k l, F.sheetNull.IsMeasIn N (E k l) := fun k l =>
    isMeasIn_of_subset (N' := N ∩ D.V k)
      (@MeasurableSet.inter Obj (borel Obj) _ _ hN.1.1.measurableSet_borel
        (MeasurableSpace.measurableSet_generateFrom (D.isOpen k)))
      (fun y hy => hy.1.1)
      ((F.sheetIntegration hn).isMeasIn_tangent_eq _ (D.mem k) _ (D'.mem l) _ _)
  have e : {y | y ∈ N ∩ N' ∧ o.tangent y = o'.tangent y} = ⋃ k, ⋃ l, E k l := by
    ext y
    simp only [mem_iUnion, hE, mem_ofPred_eq, mem_inter_iff]
    constructor
    · rintro ⟨⟨hy, hy'⟩, ht⟩
      obtain ⟨k, hk⟩ := mem_iUnion.1 (D.cover hy)
      obtain ⟨l, hl⟩ := mem_iUnion.1 (D'.cover hy')
      refine ⟨k, l, ⟨⟨hy, hk⟩, hy', hl⟩, ?_⟩
      rw [MPolyfold.SubmanifoldOrientation.restrict_tangent _ _ hk,
        MPolyfold.SubmanifoldOrientation.restrict_tangent _ _ hl]
      exact ht
    · rintro ⟨k, l, ⟨⟨hy, hk⟩, hy', hl⟩, ht⟩
      refine ⟨⟨hy, hy'⟩, ?_⟩
      rw [MPolyfold.SubmanifoldOrientation.restrict_tangent _ _ hk,
        MPolyfold.SubmanifoldOrientation.restrict_tangent _ _ hl] at ht
      exact ht
  rw [e]
  exact @MeasurableSet.iUnion Obj ℕ (F.sheetNull.sheetSigma N) _ _ fun k =>
    @MeasurableSet.iUnion Obj ℕ (F.sheetNull.sheetSigma N) _ _ fun l => hEm k l

theorem msInteg_hasSum (hn : 0 < n) (ω : Ω) (hN : N ∈ F.msheets) {m : ℕ}
    (o : X.PObj.SubmanifoldOrientation N m) (A : ℕ → Set Obj) (hAN : ∀ k, A k ⊆ N)
    (hAm : ∀ k, F.sheetNull.IsMeasIn N (A k)) (hd : Pairwise (Function.onFun Disjoint A)) :
    HasSum (fun k => F.msInteg ω N o.tangent (A k)) (F.msInteg ω N o.tangent (⋃ k, A k)) := by
  rcases eq_empty_or_nonempty N with he | ⟨y, hy⟩
  · have h0 : ∀ B : Set Obj, F.msInteg ω N o.tangent B = 0 := fun B =>
      msInteg_of_inter_eq_empty ω _ (by rw [he, inter_empty])
    simp only [h0]
    exact hasSum_zero
  obtain rfl := msheets_dim_eq hN o hy
  obtain ⟨D, hD⟩ := hN.2
  have hNb := hN.1.1.measurableSet_borel
  have hUm : F.sheetNull.IsMeasIn N (⋃ k, A k) :=
    @MeasurableSet.iUnion Obj ℕ (F.sheetNull.sheetSigma N) _ _ hAm
  simp only [msInteg_eq hn hN D hD o ω (hAm _), msInteg_eq hn hN D hD o ω hUm]
  set x : ℕ → ℕ → ℝ := fun k j => D.term ω o (A j) k with hx
  have hpm : ∀ k j, F.sheetNull.IsMeasIn (N ∩ D.V k) (A j ∩ D.P k) := fun k j => by
    have := D.isMeasIn_piece hNb (hAm j) k (Q := univ) MeasurableSet.univ
    rwa [inter_univ] at this
  have ha : ∀ k, HasSum (x k) (D.term ω o (⋃ j, A j) k) := fun k => by
    have h := (F.sheetIntegration hn).integ_hasSum ω _ (D.mem k) (o.restrict (D.isOpen k))
      (fun j => A j ∩ D.P k) (fun j y hy => D.P_subset k hy.2) (hpm k)
      (fun i j hij => (hd hij).mono inter_subset_left inter_subset_left)
    rw [← iUnion_inter] at h
    exact h
  have hb : ∀ j, HasSum (fun k => x k j) (D.gInteg ω o (A j)) := fun j =>
    (D.summable_term hD ω o (A j)).hasSum
  have hs : Summable fun p : ℕ × ℕ => x p.1 p.2 :=
    D.summable_double hD ω x (fun k j => A j ∩ D.P k) (fun k j y hy => hy.2) hpm
      (fun k i j hij => (hd hij).mono inter_subset_left inter_subset_left)
      (fun k j => F.abs_integ_le_chartAbs (D.mem k) ω _ _)
  exact hasSum_of_double hs ha hb

theorem msInteg_image (hn : 0 < n) (ω : Ω) (hN : N ∈ F.msheets) {m : ℕ}
    (o : X.PObj.SubmanifoldOrientation N m) (hM : X.PObj.IsSmoothSubmanifold N)
    {f f' : Obj → Obj} {U U' : Set Obj} (hf : X.PObj.IsScDiffeoOn X.PObj f f' U U')
    (hNU : N ⊆ U) (hmor : X.IsMorTangentOn hf N) (A : Set Obj) (hA : A ⊆ N)
    (hAm : F.sheetNull.IsMeasIn N A) :
    F.msInteg ω (f '' N) (o.mapDiffeo hM hf hNU).tangent (f '' A) =
      F.msInteg ω N o.tangent A := by
  rcases eq_empty_or_nonempty A with he | ⟨y, hy⟩
  · rw [msInteg_of_inter_eq_empty ω _ (by rw [he, image_empty, empty_inter]),
      msInteg_of_inter_eq_empty ω _ (by rw [he, empty_inter])]
  obtain rfl := msheets_dim_eq hN o (hA hy)
  obtain ⟨D, hD⟩ := hN.2
  have hNb := hN.1.1.measurableSet_borel
  have hfN := msheets_image hN hf hNU hmor
  set D' := D.image hf hNU hmor
  rw [msInteg_eq hn hfN D' (D.image_isFinite hf hNU hmor hD) _ ω (isMeasIn_image hf hNU hA hAm),
    msInteg_eq hn hN D hD o ω hAm]
  refine tsum_congr fun k => ?_
  have hk := D.mem k
  have hsub : N ∩ D.V k ⊆ U := inter_subset_left.trans hNU
  have hmork : X.IsMorTangentOn hf (N ∩ D.V k) := fun w hw => hmor w hw.1
  have hMk : X.PObj.IsSmoothSubmanifold (N ∩ D.V k) := hM.inter_isOpen (D.isOpen k)
  have hinj : InjOn f U := fun a ha b hb h => by
    rw [← hf.left_inv a ha, ← hf.left_inv b hb, h]
  have e1 : f '' A ∩ D'.P k = f '' (A ∩ D.P k) := by
    rw [ChartCover.image_P, hinj.image_inter (hA.trans hNU)
      (fun y hy => hNU (D.P_subset k hy).1)]
  have e2 := ChartCover.image_inter_eq hf hNU (D.V k)
  have hpk : A ∩ D.P k ⊆ N ∩ D.V k := fun y hy => D.P_subset k hy.2
  have hpm : F.sheetNull.IsMeasIn (N ∩ D.V k) (A ∩ D.P k) := by
    have := D.isMeasIn_piece hNb hAm k (Q := univ) MeasurableSet.univ
    rwa [inter_univ] at this
  have hfk := image_mem_sheets hk hf hsub hmork
  have hBm : F.sheetNull.IsMeasIn (f '' N ∩ D'.V k) (f '' (A ∩ D.P k)) := by
    change F.sheetNull.IsMeasIn (f '' N ∩ (U' ∩ f' ⁻¹' D.V k)) _
    rw [e2]; exact isMeasIn_image hf hsub hpk hpm
  unfold ChartCover.term
  rw [e1]
  have h1 := (F.sheetIntegration hn).integ_congr ω _ (D'.mem k) _ hfk
    ((o.mapDiffeo hM hf hNU).restrict (D'.isOpen k))
    ((o.restrict (D.isOpen k)).mapDiffeo hMk hf hsub) (f '' (A ∩ D.P k))
    (fun z hz => ⟨by change z ∈ f '' N ∩ (U' ∩ f' ⁻¹' D.V k); rw [e2]; exact image_mono hpk hz,
      image_mono hpk hz⟩) hBm fun z _ => by
      unfold MPolyfold.SubmanifoldOrientation.tangent
      change MPolyfold.OrTangent.mk _ (X.PObj.submanifoldTangent (f '' N ∩ (U' ∩ f' ⁻¹' D.V k)) z)
        _ = _
      rw [e2]
      rfl
  refine h1.trans ?_
  exact (F.sheetIntegration hn).integ_image ω _ hk (o.restrict (D.isOpen k)) hMk hf hsub hmork
    _ hpk hpm

variable (F) in
/-- **The integration of the forms of `Ω` over the oriented sheets of the class `F.msheets`**
(sheets covered by countably many graph charts, 2021 §9.5, pp. 438–445): a `SheetIntegration`
in the sense of `SheetIntegrationAbstract.lean`. -/
def msheetIntegration (hn : 0 < n) : X.SheetIntegration F.msheetNull Ω where
  integ := F.msInteg
  integ_add ω τ N g A := by
    unfold msInteg
    split_ifs with h
    · exact h.1.1.2.choose.gInteg_add hn h.1.1.2.choose_spec ω τ _ A
    · rw [add_zero]
  integ_smul a ω N g A := by
    unfold msInteg
    split_ifs with h
    · exact h.1.1.2.choose.gInteg_smul hn a ω _ A
    · rw [mul_zero]
  lindelof N hN := by
    have := msheets_secondCountable hN
    infer_instance
  inter_mem N hN V hV := msheets_inter_isOpen hN hV
  isMeasIn_inter N hN N' hN' :=
    (SheetNullSets.isMeasIn_of_borel hN'.1.1.measurableSet_borel).congr_inter (by
      rw [inter_comm N' N, inter_assoc, inter_comm N' N, ← inter_assoc, inter_self])
  isNull_tangent_ne N hN N' hN' := isNull_tangent_ne hN.1 hN'.1
  isMeasIn_tangent_eq N hN N' hN' m m' o o' := msheets_isMeasIn_tangent_eq hn hN hN' o o'
  integ_hasSum ω N hN m o A hAN hAm hd := msInteg_hasSum hn ω hN o A hAN hAm hd
  integ_null ω N hN m o A hAN hnull := by
    unfold msInteg
    split_ifs with h
    · unfold ChartCover.gInteg
      refine (tsum_congr fun k => ?_).trans tsum_zero
      exact (F.sheetIntegration hn).integ_null ω _ (h.1.1.2.choose.mem k) _ _
        (fun y hy => h.1.1.2.choose.P_subset k hy.2)
        (MPolyfold.IsHNull.mono hnull fun y hy => ⟨hy.1.1, hy.2.1⟩)
    · rfl
  integ_congr ω N hN N' hN' m m' o o' A hA hAm h := by
    rcases eq_empty_or_nonempty A with he | ⟨y, hy⟩
    · rw [msInteg_of_inter_eq_empty ω _ (by rw [he, empty_inter]),
        msInteg_of_inter_eq_empty ω _ (by rw [he, empty_inter])]
    obtain rfl := msheets_dim_eq hN o (hA hy).1
    obtain rfl := msheets_dim_eq hN' o' (hA hy).2
    have := msInteg_rel hn hN hN' o o' ω hA hAm 1 fun M M' hM hM' p p' B hB hBA hBm hp hp' => by
      rw [one_mul]
      exact (F.sheetIntegration hn).integ_congr ω M hM M' hM' p p' B hB hBm fun z hz => by
        rw [hp z hz, hp' z hz]; exact h z (hBA hz)
    rw [this, one_mul]
  integ_neg ω N hN N' hN' m m' o o' A hA hAm h := by
    rcases eq_empty_or_nonempty A with he | ⟨y, hy⟩
    · rw [msInteg_of_inter_eq_empty ω _ (by rw [he, empty_inter]),
        msInteg_of_inter_eq_empty ω _ (by rw [he, empty_inter]), neg_zero]
    obtain rfl := msheets_dim_eq hN o (hA hy).1
    obtain rfl := msheets_dim_eq hN' o' (hA hy).2
    have := msInteg_rel hn hN hN' o o' ω hA hAm (-1)
      fun M M' hM hM' p p' B hB hBA hBm hp hp' => by
      rw [neg_one_mul]
      refine (F.sheetIntegration hn).integ_neg ω M hM M' hM' p p' B hB hBm fun z hz => ?_
      have hz1 := congrArg MPolyfold.OrTangent.carrier (hp z hz)
      have hz2 := congrArg MPolyfold.OrTangent.carrier (hp' z hz)
      refine ⟨?_, by rw [hp z hz, hp' z hz]; exact (h z (hBA hz)).2⟩
      exact hz1.trans ((h z (hBA hz)).1.trans hz2.symm)
    rw [this, neg_one_mul]
  image_mem N hN f f' U U' hf hNU hmor := msheets_image hN hf hNU hmor
  isMeasIn_image N hN _ _ _ _ hf hNU _ A hA hAm := isMeasIn_image (F := F) hf hNU hA hAm
  integ_image ω N hN m o hM f f' U U' hf hNU hmor A hA hAm :=
    msInteg_image (F := F) hn ω hN o hM hf hNU hmor A hA hAm

@[simp] theorem msheetIntegration_integ (hn : 0 < n) :
    (F.msheetIntegration hn).integ = F.msInteg := rfl

/-- **On the one-chart sheets the two integrations agree.** -/
theorem msInteg_eq_integ (hn : 0 < n) (hN : N ∈ F.sheets) (o : X.PObj.SubmanifoldOrientation N n)
    (ω : Ω) {A : Set Obj} (hA : F.sheetNull.IsMeasIn N A) :
    F.msInteg ω N o.tangent A = F.integ ω N o.tangent A := by
  rw [msInteg_eq hn (sheets_subset_msheets hN) (ChartCover.single F hN)
    (ChartCover.single_isFinite hN) o ω hA]
  unfold ChartCover.gInteg
  rw [tsum_eq_single 0 fun k hk => by
    unfold ChartCover.term
    rw [ChartCover.single_P_eq_empty hN hk, inter_empty]
    exact integ_of_inter_eq_empty ω _ (empty_inter _)]
  unfold ChartCover.term
  have hP : A ∩ (ChartCover.single F hN).P 0 = A ∩ N := by
    ext y; simp only [ChartCover.P, ChartCover.W, ChartCover.single, mem_inter_iff,
      mem_ofPred_eq, mem_univ, not_lt_zero, IsEmpty.forall_iff, implies_true, and_true]
  rw [hP]
  have hAN : F.sheetNull.IsMeasIn (N ∩ univ) (A ∩ N) :=
    isMeasIn_of_superset inter_subset_left (SheetNullSets.isMeasIn_inter_iff.2 hA)
  have e := (F.sheetIntegration hn).integ_congr ω _ ((ChartCover.single F hN).mem 0) N hN
    (o.restrict isOpen_univ) o (A ∩ N) (fun y hy => ⟨⟨hy.2, mem_univ y⟩, hy.2⟩) hAN
    fun y _ => o.restrict_tangent isOpen_univ (mem_univ y)
  refine e.trans ?_
  change F.integ ω N o.tangent (A ∩ N) = _
  rw [integ_eq hN o, integ_eq hN o]
  unfold chartInteg
  rw [inter_assoc, inter_self]

end FormEval

end EpGroupoid

end Polyfold
