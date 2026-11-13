import Polyfold.Chapter9.GapP2_E4_ChartAbs

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5 "Integration and Stokes", pp. 438–445 (gap G.107).  Numbers and pages
are the 2021 text's.

# Sheets covered by several graph charts: countable chart covers and the glued integral

`GapP2_E3_SheetIntegration.lean` integrates over the sheets of the class `F.sheets` (one graph
chart).  Here a sheet `N` is covered by countably many open sets `V k` with `N ∩ V k ∈ F.sheets`
(`ChartCover`); the pieces `P k = N ∩ V k \ ⋃_{j<k} V j` are disjoint Borel sets, and

  `∫_A ω|(N, o) = ∑ₖ ∫_{A ∩ P k} ω|(N ∩ V k, o)`.

The series converges absolutely when `∑ₖ ∫_{P k} |ω| < ∞` (`ChartCover.IsFinite`; the integrals
of `|ω|` do not depend on the charts, `GapP2_E4_ChartAbs.lean`).

* `ChartCover.gInteg_eq_of`: **the glued integral does not depend on the cover**, and two sheets
  give equal (opposite) glued integrals over a common measurable set where their oriented
  tangent spaces agree (are opposite): a double series over the pieces of the two covers.
* `ChartCover.restrict`, `ChartCover.image`, `ChartCover.single`: covers of open pieces, of
  images under the sc-diffeomorphisms given by morphisms, and of sheets of `F.sheets`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module
open scoped symmDiff

noncomputable section

namespace Polyfold

universe u

/-- **Interchanging a double series**: if `x` is summable on `ℕ × ℕ`, `∑ₗ x k l = a k` and
`∑ₖ x k l = b l`, then `∑ b = ∑ a`. -/
theorem hasSum_of_double {x : ℕ → ℕ → ℝ} {a b : ℕ → ℝ}
    (hs : Summable fun p : ℕ × ℕ => x p.1 p.2) (ha : ∀ k, HasSum (x k) (a k))
    (hb : ∀ l, HasSum (fun k => x k l) (b l)) : HasSum b (∑' k, a k) := by
  have h1 : HasSum a (∑' p : ℕ × ℕ, x p.1 p.2) := hs.hasSum.prod_fiberwise ha
  have h2 : HasSum (fun p : ℕ × ℕ => x p.2 p.1) (∑' p : ℕ × ℕ, x p.1 p.2) :=
    (Equiv.prodComm ℕ ℕ).hasSum_iff.2 hs.hasSum
  rw [h1.tsum_eq]
  exact h2.prod_fiberwise hb

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {n : ℕ} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω] (F : X.FormEval n Ω)

namespace FormEval

/-! ### Measurable subsets of sheets -/

section Meas

variable {F}

theorem isMeasIn_of_superset {N N' A : Set Obj} (hN'N : N' ⊆ N)
    (h : F.sheetNull.IsMeasIn N A) : F.sheetNull.IsMeasIn N' A := by
  obtain ⟨B, hB, hnull⟩ := h
  refine ⟨B, hB, MPolyfold.IsHNull.mono hnull ?_⟩
  rintro y ⟨hy, hyN'⟩
  refine ⟨?_, hN'N hyN'⟩
  rcases hy with ⟨⟨hA, -⟩, hn⟩ | ⟨⟨hB', -⟩, hn⟩
  · exact Or.inl ⟨⟨hA, hN'N hyN'⟩, fun h => hn ⟨h.1, hyN'⟩⟩
  · exact Or.inr ⟨⟨hB', hN'N hyN'⟩, fun h => hn ⟨h.1, hyN'⟩⟩

theorem isMeasIn_of_subset {N N' A : Set Obj} (hN' : MeasurableSet[borel Obj] N')
    (hAN' : A ⊆ N') (h : F.sheetNull.IsMeasIn N' A) : F.sheetNull.IsMeasIn N A := by
  obtain ⟨B, hB, hnull⟩ := h
  refine ⟨B ∩ N', @MeasurableSet.inter Obj (borel Obj) _ _ hB hN', MPolyfold.IsHNull.mono hnull ?_⟩
  rintro y ⟨hy, hyN⟩
  rcases hy with ⟨⟨hA, -⟩, hn⟩ | ⟨⟨⟨hB', hy'⟩, -⟩, hn⟩
  · exact ⟨Or.inl ⟨⟨hA, hAN' hA⟩, fun h => hn ⟨⟨h.1, hAN' hA⟩, hyN⟩⟩, hAN' hA⟩
  · exact ⟨Or.inr ⟨⟨hB', hy'⟩, fun h => hn ⟨h.1, hyN⟩⟩, hy'⟩

theorem isMeasIn_transfer {N N' A : Set Obj} (hN : MeasurableSet[borel Obj] N)
    (hA : A ⊆ N ∩ N') (h : F.sheetNull.IsMeasIn N A) : F.sheetNull.IsMeasIn N' A := by
  obtain ⟨B, hB, hnull⟩ := h
  refine ⟨B ∩ N, @MeasurableSet.inter Obj (borel Obj) _ _ hB hN, MPolyfold.IsHNull.mono hnull ?_⟩
  rintro y ⟨hy, hyN'⟩
  rcases hy with ⟨⟨hyA, -⟩, hn⟩ | ⟨⟨⟨hyB, hyN⟩, -⟩, hn⟩
  · exact ⟨Or.inl ⟨⟨hyA, (hA hyA).1⟩, fun h => hn ⟨⟨h.1, (hA hyA).1⟩, hyN'⟩⟩, (hA hyA).1⟩
  · exact ⟨Or.inr ⟨⟨hyB, hyN⟩, fun h => hn ⟨h.1, hyN'⟩⟩, hyN⟩

end Meas

/-! ### Countable chart covers -/

/-- **A countable chart cover of `N`**: open sets `V k` covering `N` with `N ∩ V k` in the
class `F.sheets` (one graph chart, all forms absolutely integrable). -/
structure ChartCover (N : Set Obj) where
  V : ℕ → Set Obj
  isOpen : ∀ k, IsOpen (V k)
  cover : N ⊆ ⋃ k, V k
  mem : ∀ k, N ∩ V k ∈ F.sheets

namespace ChartCover

variable {F} {N : Set Obj} (D : F.ChartCover N)

/-- The Borel set `V k \ ⋃_{j<k} V j`. -/
def W (k : ℕ) : Set Obj := {y | y ∈ D.V k ∧ ∀ j < k, y ∉ D.V j}

/-- **The pieces** `P k = N ∩ V k \ ⋃_{j<k} V j`. -/
def P (k : ℕ) : Set Obj := N ∩ D.W k

theorem P_subset (k : ℕ) : D.P k ⊆ N ∩ D.V k := fun _ hy => ⟨hy.1, hy.2.1⟩

theorem measurableSet_W (k : ℕ) : MeasurableSet[borel Obj] (D.W k) := by
  let _ : MeasurableSpace Obj := borel Obj
  have e : D.W k = D.V k ∩ ⋂ j ∈ Finset.range k, (D.V j)ᶜ := by
    ext y
    simp only [W, mem_ofPred_eq, mem_inter_iff, mem_iInter, Finset.mem_range, mem_compl_iff]
  rw [e]
  exact (MeasurableSpace.measurableSet_generateFrom (D.isOpen k)).inter
    (Finset.measurableSet_biInter _ fun j _ =>
      (MeasurableSpace.measurableSet_generateFrom (D.isOpen j)).compl)

theorem measurableSet_P (hN : MeasurableSet[borel Obj] N) (k : ℕ) :
    MeasurableSet[borel Obj] (D.P k) :=
  @MeasurableSet.inter Obj (borel Obj) _ _ hN (D.measurableSet_W k)

theorem disjoint_P : Pairwise (Function.onFun Disjoint D.P) := by
  intro i j hij
  refine disjoint_left.2 fun y hi hj => ?_
  rcases lt_or_gt_of_ne hij with h | h
  · exact hj.2.2 i h hi.2.1
  · exact hi.2.2 j h hj.2.1

theorem exists_mem_P {y : Obj} (hy : y ∈ N) : ∃ k, y ∈ D.P k := by
  classical
  have hex : ∃ k, y ∈ D.V k := mem_iUnion.1 (D.cover hy)
  exact ⟨Nat.find hex, hy, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩

theorem iUnion_P : ⋃ k, D.P k = N := by
  ext y
  refine ⟨fun hy => ?_, fun hy => mem_iUnion.2 (D.exists_mem_P hy)⟩
  obtain ⟨k, hk⟩ := mem_iUnion.1 hy
  exact hk.1

/-- `∫ |ω|` over the pieces is summable. -/
def IsFinite : Prop :=
  ∀ ω : Ω, Summable fun k => F.chartAbs (chart (D.mem k)) ω (D.P k)

end ChartCover

/-- **The class of sheets covered by countably many graph charts with `∫ |ω| < ∞`**: the
`n`-dimensional submanifolds `N` with a chart cover on whose pieces the integrals of `|ω|` are
summable, for every form `ω`. -/
def msheets : Set (Set Obj) :=
  {N | X.PObj.IsSubmanifoldOfDim N n ∧ ∃ D : F.ChartCover N, D.IsFinite}

/-- **The null sets** (Definition 9.4.5, `IsHNull`) on the class `F.msheets`. -/
def msheetNull : SheetNullSets F.msheets :=
  X.PObj.hNullSets n F.msheets fun N hN hne => by
    obtain ⟨y, hy⟩ := hne
    exact MPolyfold.not_isHNull_of_hasDimAt hN.1.1 (hN.1.2 y hy)

theorem msheetNull_isMeasIn_iff {N A : Set Obj} :
    F.msheetNull.IsMeasIn N A ↔ F.sheetNull.IsMeasIn N A := Iff.rfl

/-- `|∫_B ω|(M, g)| ≤ ∫_B |ω|` for a sheet of the class `F.sheets`. -/
theorem abs_integ_le_chartAbs {M : Set Obj} (hM : M ∈ F.sheets) (ω : Ω)
    (g : Obj → X.PObj.OrTangent) (B : Set Obj) :
    |F.integ ω M g B| ≤ F.chartAbs (chart hM) ω B := by
  unfold integ
  split_ifs with h
  · exact F.abs_chartInteg_le _ ω g B
  · rw [abs_zero]; exact F.chartAbs_nonneg _ ω B

namespace ChartCover

variable {F} {N : Set Obj} (D : F.ChartCover N)

/-- The term `∫_{A ∩ P k} ω|(N ∩ V k, o)` of the glued integral. -/
def term (ω : Ω) (o : X.PObj.SubmanifoldOrientation N n) (A : Set Obj) (k : ℕ) : ℝ :=
  F.integ ω (N ∩ D.V k) (o.restrict (D.isOpen k)).tangent (A ∩ D.P k)

/-- **The glued integral** `∑ₖ ∫_{A ∩ P k} ω|(N ∩ V k, o)`. -/
def gInteg (ω : Ω) (o : X.PObj.SubmanifoldOrientation N n) (A : Set Obj) : ℝ :=
  ∑' k, D.term ω o A k

theorem abs_term_le (ω : Ω) (o : X.PObj.SubmanifoldOrientation N n) (A : Set Obj) (k : ℕ) :
    |D.term ω o A k| ≤ F.chartAbs (chart (D.mem k)) ω (D.P k) :=
  (F.abs_integ_le_chartAbs (D.mem k) ω _ _).trans
    (F.chartAbs_mono _ ω (integrableOn_chart (D.mem k) ω) fun _ hy => hy.1.2)

theorem summable_term (hD : D.IsFinite) (ω : Ω) (o : X.PObj.SubmanifoldOrientation N n)
    (A : Set Obj) : Summable (D.term ω o A) :=
  Summable.of_norm_bounded (hD ω) fun k => by
    rw [Real.norm_eq_abs]; exact D.abs_term_le ω o A k

theorem gInteg_add (hn : 0 < n) (hD : D.IsFinite) (ω τ : Ω)
    (o : X.PObj.SubmanifoldOrientation N n) (A : Set Obj) :
    D.gInteg (ω + τ) o A = D.gInteg ω o A + D.gInteg τ o A := by
  unfold gInteg
  rw [← (D.summable_term hD ω o A).tsum_add (D.summable_term hD τ o A)]
  exact tsum_congr fun k => (F.sheetIntegration hn).integ_add ω τ _ _ _

theorem gInteg_smul (hn : 0 < n) (a : ℝ) (ω : Ω) (o : X.PObj.SubmanifoldOrientation N n)
    (A : Set Obj) : D.gInteg (a • ω) o A = a * D.gInteg ω o A := by
  unfold gInteg
  rw [← tsum_mul_left]
  exact tsum_congr fun k => (F.sheetIntegration hn).integ_smul a ω _ _ _

/-- **Summability of a double family** of integrals over subsets of the pieces. -/
theorem summable_double (hD : D.IsFinite) (ω : Ω) (x : ℕ → ℕ → ℝ) (C : ℕ → ℕ → Set Obj)
    (hC : ∀ k l, C k l ⊆ D.P k) (hCm : ∀ k l, F.sheetNull.IsMeasIn (N ∩ D.V k) (C k l))
    (hCd : ∀ k, Pairwise (Function.onFun Disjoint (C k)))
    (hx : ∀ k l, |x k l| ≤ F.chartAbs (chart (D.mem k)) ω (C k l)) :
    Summable fun p : ℕ × ℕ => x p.1 p.2 := by
  set b : ℕ × ℕ → ℝ := fun p => F.chartAbs (chart (D.mem p.1)) ω (C p.1 p.2) with hb
  have hb0 : 0 ≤ b := fun p => F.chartAbs_nonneg _ ω _
  have hsum : ∀ k, HasSum (fun l => b (k, l))
      (F.chartAbs (chart (D.mem k)) ω (⋃ l, C k l)) := fun k =>
    F.chartAbs_hasSum _ ω (integrableOn_chart (D.mem k) ω) (C k)
      (fun l => nullMeasurableSet_coord_image _ (hCm k l)) (hCd k)
  have hbs : Summable b := by
    refine (summable_prod_of_nonneg hb0).2 ⟨fun k => (hsum k).summable, ?_⟩
    refine Summable.of_nonneg_of_le (fun k => tsum_nonneg fun l => hb0 (k, l)) (fun k => ?_)
      (hD ω)
    rw [(hsum k).tsum_eq]
    exact F.chartAbs_mono _ ω (integrableOn_chart (D.mem k) ω) fun y hy => by
      obtain ⟨l, hl⟩ := mem_iUnion.1 hy.1
      exact hC k l hl
  exact Summable.of_norm_bounded hbs fun p => by rw [Real.norm_eq_abs]; exact hx p.1 p.2

/-- Cutting the integral over a sheet of `F.sheets` along countably many disjoint Borel sets
covering the domain. -/
theorem hasSum_integ_split (hn : 0 < n) {M : Set Obj} (hM : M ∈ F.sheets) {m : ℕ}
    (o : X.PObj.SubmanifoldOrientation M m) (ω : Ω) {B : Set Obj} (hB : B ⊆ M)
    (hBm : F.sheetNull.IsMeasIn M B) (Q : ℕ → Set Obj) (hQ : ∀ l, MeasurableSet[borel Obj] (Q l))
    (hQd : Pairwise (Function.onFun Disjoint Q)) (hcov : B ⊆ ⋃ l, Q l) :
    HasSum (fun l => F.integ ω M o.tangent (B ∩ Q l)) (F.integ ω M o.tangent B) := by
  have h := (F.sheetIntegration hn).integ_hasSum ω M hM o (fun l => B ∩ Q l)
    (fun l => inter_subset_left.trans hB)
    (fun l => @MeasurableSet.inter Obj (F.sheetNull.sheetSigma M) _ _ hBm
      (SheetNullSets.isMeasIn_of_borel (hQ l)))
    (fun i j hij => (hQd hij).mono inter_subset_right inter_subset_right)
  have e : (⋃ l, B ∩ Q l) = B := by
    rw [← inter_iUnion]; exact inter_eq_left.2 hcov
  rw [e] at h
  exact h

/-- **The glued integrals over two sheets**: if on every piece `A ∩ P k ∩ P' l` the integral
over `N ∩ V k` is `s` times the integral over `N' ∩ V' l`, the glued integrals are in the same
relation (a double series over the pieces of the two covers). -/
theorem gInteg_eq_of (hn : 0 < n) {N' : Set Obj} (D' : F.ChartCover N') (hD : D.IsFinite)
    (hNb : MeasurableSet[borel Obj] N) (hN'b : MeasurableSet[borel Obj] N') (ω : Ω)
    (o : X.PObj.SubmanifoldOrientation N n) (o' : X.PObj.SubmanifoldOrientation N' n)
    {A : Set Obj} (hA : A ⊆ N ∩ N') (hAm : F.sheetNull.IsMeasIn N A) (s : ℝ)
    (hrel : ∀ k l, F.integ ω (N ∩ D.V k) (o.restrict (D.isOpen k)).tangent
        (A ∩ D.P k ∩ D'.P l) =
      s * F.integ ω (N' ∩ D'.V l) (o'.restrict (D'.isOpen l)).tangent (A ∩ D.P k ∩ D'.P l)) :
    D.gInteg ω o A = s * D'.gInteg ω o' A := by
  set x : ℕ → ℕ → ℝ := fun k l =>
    F.integ ω (N ∩ D.V k) (o.restrict (D.isOpen k)).tangent (A ∩ D.P k ∩ D'.P l) with hx
  have hAm' : F.sheetNull.IsMeasIn N' A := isMeasIn_transfer hNb hA hAm
  have hmk : ∀ k, F.sheetNull.IsMeasIn (N ∩ D.V k) (A ∩ D.P k) := fun k =>
    isMeasIn_of_superset inter_subset_left
      (@MeasurableSet.inter Obj (F.sheetNull.sheetSigma N) _ _ hAm
        (SheetNullSets.isMeasIn_of_borel (D.measurableSet_P hNb k)))
  have hmk' : ∀ l, F.sheetNull.IsMeasIn (N' ∩ D'.V l) (A ∩ D'.P l) := fun l =>
    isMeasIn_of_superset inter_subset_left
      (@MeasurableSet.inter Obj (F.sheetNull.sheetSigma N') _ _ hAm'
        (SheetNullSets.isMeasIn_of_borel (D'.measurableSet_P hN'b l)))
  have ha : ∀ k, HasSum (x k) (D.term ω o A k) := fun k =>
    hasSum_integ_split hn (D.mem k) _ ω (fun y hy => D.P_subset k hy.2) (hmk k) D'.P
      (D'.measurableSet_P hN'b) D'.disjoint_P (fun y hy => by
        rw [D'.iUnion_P]; exact (hA hy.1).2)
  have hb : ∀ l, HasSum (fun k => x k l) (s * D'.term ω o' A l) := fun l => by
    have h := hasSum_integ_split hn (D'.mem l) (o'.restrict (D'.isOpen l)) ω
      (B := A ∩ D'.P l) (fun y hy => D'.P_subset l hy.2) (hmk' l) D.P
      (D.measurableSet_P hNb) D.disjoint_P (fun y hy => by
        rw [D.iUnion_P]; exact (hA hy.1).1)
    have e : (fun k => x k l) = fun k => s * F.integ ω (N' ∩ D'.V l)
        (o'.restrict (D'.isOpen l)).tangent (A ∩ D'.P l ∩ D.P k) := by
      funext k
      change F.integ ω (N ∩ D.V k) (o.restrict (D.isOpen k)).tangent (A ∩ D.P k ∩ D'.P l) = _
      rw [hrel k l, inter_right_comm]
    rw [e]
    exact h.mul_left s
  have hs : Summable fun p : ℕ × ℕ => x p.1 p.2 :=
    D.summable_double hD ω x (fun k l => A ∩ D.P k ∩ D'.P l) (fun k l y hy => hy.1.2)
      (fun k l => @MeasurableSet.inter Obj (F.sheetNull.sheetSigma (N ∩ D.V k)) _ _ (hmk k)
        (SheetNullSets.isMeasIn_of_borel (D'.measurableSet_P hN'b l)))
      (fun k i j hij => (D'.disjoint_P hij).mono inter_subset_right inter_subset_right)
      (fun k l => F.abs_integ_le_chartAbs (D.mem k) ω _ _)
  have h := hasSum_of_double hs ha hb
  unfold gInteg
  rw [← tsum_mul_left]
  exact h.tsum_eq.symm

/-! ### Covers of sheets of `F.sheets`, of open pieces and of images -/

/-- Two graph charts of two sheets of the class give the same `∫_B |ω|` on a common measurable
`B` where the tangent spaces agree. -/
theorem chartAbs_eq_of_mem {M M' : Set Obj} (hM : M ∈ F.sheets) (hM' : M' ∈ F.sheets)
    (c : X.PObj.GraphChart n M) (c' : X.PObj.GraphChart n M') (ω : Ω) {B : Set Obj}
    (hB : B ⊆ M ∩ M') (hBm : F.sheetNull.IsMeasIn M B)
    (hT : ∀ y ∈ B, X.PObj.submanifoldTangent M y = X.PObj.submanifoldTangent M' y) :
    F.chartAbs c ω B = F.chartAbs c' ω B := by
  have hBM : B ∩ M = B := inter_eq_left.2 fun y hy => (hB hy).1
  have h := nullMeasurableSet_coord_image c hBm
  rw [hBM] at h
  exact F.chartAbs_congr hM.1 hM'.1 c c' ω hB h hT

variable (F) in
/-- **The one-piece cover** of a sheet of `F.sheets`. -/
def single {M : Set Obj} (hM : M ∈ F.sheets) : F.ChartCover M where
  V _ := univ
  isOpen _ := isOpen_univ
  cover y _ := mem_iUnion.2 ⟨0, mem_univ y⟩
  mem _ := inter_mem_sheets hM isOpen_univ

theorem single_P_eq_empty {M : Set Obj} (hM : M ∈ F.sheets) {k : ℕ} (hk : k ≠ 0) :
    (single F hM).P k = ∅ :=
  eq_empty_of_forall_notMem fun _ hy => hy.2.2 0 (Nat.pos_of_ne_zero hk) (mem_univ _)

theorem single_isFinite {M : Set Obj} (hM : M ∈ F.sheets) : (single F hM).IsFinite := fun ω =>
  (hasSum_single 0 fun k hk => by
    unfold chartAbs
    rw [single_P_eq_empty hM hk, empty_inter, image_empty, Measure.restrict_empty,
      integral_zero_measure]).summable

theorem coe_restrict_eq (W : Set Obj) (k : ℕ) :
    (N ∩ W) ∩ (D.V k ∩ W) = (N ∩ D.V k) ∩ W := by
  ext y; simp only [mem_inter_iff]; tauto

/-- **The cover of an open piece** `N ∩ W`. -/
def restrict {W : Set Obj} (hW : IsOpen W) : F.ChartCover (N ∩ W) where
  V k := D.V k ∩ W
  isOpen k := (D.isOpen k).inter hW
  cover y hy := by
    obtain ⟨k, hk⟩ := mem_iUnion.1 (D.cover hy.1)
    exact mem_iUnion.2 ⟨k, hk, hy.2⟩
  mem k := (D.coe_restrict_eq W k).symm ▸ inter_mem_sheets (D.mem k) hW

theorem restrict_P_subset {W : Set Obj} (hW : IsOpen W) (k : ℕ) :
    (D.restrict hW).P k ⊆ D.P k ∩ W :=
  fun _ hy => ⟨⟨hy.1.1, hy.2.1.1, fun j hj hjV => hy.2.2 j hj ⟨hjV, hy.1.2⟩⟩, hy.1.2⟩

theorem restrict_isFinite (hN : X.PObj.IsSmoothSubmanifold N) (hD : D.IsFinite) {W : Set Obj}
    (hW : IsOpen W) : (D.restrict hW).IsFinite := fun ω => by
  refine Summable.of_nonneg_of_le (fun k => F.chartAbs_nonneg _ ω _) (fun k => ?_) (hD ω)
  have hWb : MeasurableSet[borel Obj] W := MeasurableSpace.measurableSet_generateFrom hW
  have hNWb : MeasurableSet[borel Obj] (N ∩ W) :=
    @MeasurableSet.inter Obj (borel Obj) _ _ hN.measurableSet_borel hWb
  have hPb := (D.restrict hW).measurableSet_P hNWb k
  have hsub : (D.restrict hW).P k ⊆ ((N ∩ W) ∩ (D.V k ∩ W)) ∩ (N ∩ D.V k) := fun y hy =>
    ⟨(D.restrict hW).P_subset k hy, D.P_subset k (D.restrict_P_subset hW k hy).1⟩
  have e := chartAbs_eq_of_mem ((D.restrict hW).mem k) (D.mem k) (chart ((D.restrict hW).mem k))
    (chart (D.mem k)) ω hsub (SheetNullSets.isMeasIn_of_borel hPb) fun y hy => by
      have h1 := (D.restrict_P_subset hW k hy)
      change X.PObj.submanifoldTangent ((N ∩ W) ∩ (D.V k ∩ W)) y = _
      rw [MPolyfold.submanifoldTangent_inter_isOpen ((D.isOpen k).inter hW) ⟨h1.1.2.1, h1.2⟩,
        MPolyfold.submanifoldTangent_inter_isOpen hW h1.2,
        MPolyfold.submanifoldTangent_inter_isOpen (D.isOpen k) h1.1.2.1]
  rw [e]
  exact F.chartAbs_mono _ ω (integrableOn_chart (D.mem k) ω) fun y hy =>
    (D.restrict_P_subset hW k hy.1).1

section Image

variable {f f' : Obj → Obj} {U U' : Set Obj} (hf : X.PObj.IsScDiffeoOn X.PObj f f' U U')

include hf in
theorem image_inter_eq (hNU : N ⊆ U) (V : Set Obj) :
    f '' N ∩ (U' ∩ f' ⁻¹' V) = f '' (N ∩ V) := by
  ext z
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, -, hV⟩
    rw [mem_preimage, hf.left_inv y (hNU hy)] at hV
    exact ⟨y, ⟨hy, hV⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hV⟩, rfl⟩
    refine ⟨⟨y, hy, rfl⟩, hf.mapsTo (hNU hy), ?_⟩
    rw [mem_preimage, hf.left_inv y (hNU hy)]
    exact hV

/-- **The image cover** of `f(N)` for an sc-diffeomorphism whose tangent maps are those of
morphisms. -/
def image (hNU : N ⊆ U) (hmor : X.IsMorTangentOn hf N) : F.ChartCover (f '' N) where
  V k := U' ∩ f' ⁻¹' D.V k
  isOpen k := hf.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage hf.isScSmoothOn_inv.isOpen
    (D.isOpen k)
  cover := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨k, hk⟩ := mem_iUnion.1 (D.cover hy)
    refine mem_iUnion.2 ⟨k, hf.mapsTo (hNU hy), ?_⟩
    rw [mem_preimage, hf.left_inv y (hNU hy)]
    exact hk
  mem k := (image_inter_eq hf hNU (D.V k)).symm ▸
    image_mem_sheets (D.mem k) hf (inter_subset_left.trans hNU) fun w hw => hmor w hw.1

theorem image_P (hNU : N ⊆ U) (hmor : X.IsMorTangentOn hf N) (k : ℕ) :
    (D.image hf hNU hmor).P k = f '' D.P k := by
  ext z
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, ⟨-, hk⟩, hj⟩
    have hl := hf.left_inv y (hNU hy)
    rw [mem_preimage, hl] at hk
    refine ⟨y, ⟨hy, hk, fun j hjk hjV => hj j hjk ⟨hf.mapsTo (hNU hy), ?_⟩⟩, rfl⟩
    rw [mem_preimage, hl]; exact hjV
  · rintro ⟨y, ⟨hy, hk, hj⟩, rfl⟩
    have hl := hf.left_inv y (hNU hy)
    refine ⟨⟨y, hy, rfl⟩, ⟨hf.mapsTo (hNU hy), by rw [mem_preimage, hl]; exact hk⟩,
      fun j hjk hjV => hj j hjk ?_⟩
    have := hjV.2
    rwa [mem_preimage, hl] at this

theorem image_isFinite (hNU : N ⊆ U) (hmor : X.IsMorTangentOn hf N) (hD : D.IsFinite) :
    (D.image hf hNU hmor).IsFinite := fun ω => by
  refine (hD ω).congr fun k => ?_
  have hk := D.mem k
  have hsub : N ∩ D.V k ⊆ U := inter_subset_left.trans hNU
  have e := image_inter_eq hf hNU (D.V k)
  set c := (chart hk).mapDiffeo hk.1.1 hf hsub
  have hPk : D.P k ⊆ N ∩ D.V k := D.P_subset k
  have hPm : F.sheetNull.IsMeasIn (N ∩ D.V k) (D.P k) :=
    SheetNullSets.isMeasIn_of_borel (D.measurableSet_W k) |>.congr_inter (by
      ext y; simp only [P, mem_inter_iff]; constructor
      · rintro ⟨hW, hy, hV⟩; exact ⟨⟨hy, hW⟩, hy, hV⟩
      · rintro ⟨⟨hy, hW⟩, -, hV⟩; exact ⟨hW, hy, hV⟩)
  have hfPm : F.sheetNull.IsMeasIn (f '' N ∩ (U' ∩ f' ⁻¹' D.V k)) (f '' D.P k) := by
    rw [e]; exact isMeasIn_image hf hsub hPk hPm
  have hfP : f '' D.P k ⊆ (f '' N ∩ (U' ∩ f' ⁻¹' D.V k)) ∩ f '' (N ∩ D.V k) := fun z hz =>
    ⟨e ▸ image_mono hPk hz, image_mono hPk hz⟩
  have h1 := chartAbs_eq_of_mem ((D.image hf hNU hmor).mem k)
    (image_mem_sheets hk hf hsub fun w hw => hmor w hw.1) (chart ((D.image hf hNU hmor).mem k))
    c ω hfP hfPm fun y _ => by
      change X.PObj.submanifoldTangent (f '' N ∩ (U' ∩ f' ⁻¹' D.V k)) y = _
      rw [e]
  have hnm : NullMeasurableSet ((chart hk).coord '' D.P k) volume := by
    have := nullMeasurableSet_coord_image (chart hk) hPm
    rwa [inter_eq_left.2 hPk] at this
  rw [image_P, h1]
  exact (F.chartAbs_mapDiffeo hk.1.1 (chart hk) hf hsub (fun w hw => hmor w hw.1) ω hPk hnm).symm

end Image

end ChartCover

end FormEval

end EpGroupoid

end Polyfold
