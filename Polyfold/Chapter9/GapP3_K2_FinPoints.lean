import Polyfold.Chapter9.GapP3_K2_ZeroForms
import Polyfold.Chapter9.GapP2_E5_BoundaryNullSigma

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, Theorems 9.5.15 and 9.5.16 for `n = 1` (p. 449), gap G.109.  Numbers
and pages are the 2021 text's.

# Integration of `0`-forms over finite sets of oriented points

E1's `pointIntegration` integrates over sheets with at most one point.  The boundary sheet
`∂₁Mᵢ` of an arbitrary `1`-dimensional oriented tame structure is a finite set of points
(`GapP3_K2_AllStructuresDim1`), and the text's `∫_{Kᵢ} ω|(∂₁Mᵢ, o)` is then the signed sum
`∑_{p ∈ Kᵢ} ±ω(p)`.  This file gives that integration as a `SheetIntegration`.

* `finPointSheets X`: the finite sets of smooth points.
* `finPointInteg f N g A = ∑_{p ∈ N ∩ A} frameSign (g p) * f p` (for finite `N`).
* **`finPointIntegration X`**: all fields of `SheetIntegration` hold, with E2's null sets of
  dimension `0` (`SheetNullSets.point`).
* `finPointInteg_eq_pointInteg`: on sheets with at most one point it is E1's `pointInteg`.
* **`EP.finZeroFormIntegration`**: the integration of `Ω⁰_{ep,∞}(X)` over finite sets of oriented
  points; it agrees with `EP.zeroFormIntegration` on `pointSheets`
  (`finZeroFormIntegration_integ_eq`).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory
open scoped symmDiff

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

variable (X : EpGroupoid Obj Mor) in
/-- The sheets of dimension `0` with finitely many points: the finite sets of smooth points. -/
def finPointSheets : Set (Set Obj) := {N | N.Finite ∧ N ⊆ X.PObj.smoothSet}

variable {X : EpGroupoid Obj Mor}

theorem pointSheets_subset_finPointSheets : pointSheets X ⊆ finPointSheets X := by
  rintro N (rfl | ⟨p, hp, rfl⟩)
  · exact ⟨finite_empty, empty_subset _⟩
  · exact ⟨finite_singleton p, singleton_subset_iff.2 hp⟩

open scoped Classical in
/-- `∫_A f|(N, o) = ∑_{p ∈ N ∩ A} ± f(p)` for a finite set `N` of oriented points (`0` if `N` is
infinite). -/
def finPointInteg (f : Obj → ℝ) (N : Set Obj) (g : Obj → X.PObj.OrTangent) (A : Set Obj) : ℝ :=
  if h : N.Finite then ∑ p ∈ h.toFinset, A.indicator (fun p => frameSign (g p) * f p) p else 0

theorem finPointInteg_coe {f : Obj → ℝ} {N : Set Obj} {g : Obj → X.PObj.OrTangent}
    (hN : N.Finite) (s : Finset Obj) (hs : (s : Set Obj) ⊆ N) :
    finPointInteg f N g s = ∑ p ∈ s, frameSign (g p) * f p := by
  rw [finPointInteg, dif_pos hN]
  exact Finset.sum_indicator_subset _ (hN.subset_toFinset.2 hs)

theorem finPointInteg_of_subset {f : Obj → ℝ} {N : Set Obj} {g : Obj → X.PObj.OrTangent}
    (hN : N.Finite) {A : Set Obj} (hA : A ⊆ N) (hAf : A.Finite) :
    finPointInteg f N g A = ∑ p ∈ hAf.toFinset, frameSign (g p) * f p := by
  conv_lhs => rw [← hAf.coe_toFinset]
  exact finPointInteg_coe hN _ (by rw [hAf.coe_toFinset]; exact hA)

theorem finPointInteg_inter (f : Obj → ℝ) (N : Set Obj) (g : Obj → X.PObj.OrTangent)
    (A : Set Obj) : finPointInteg f N g A = finPointInteg f N g (A ∩ N) := by
  unfold finPointInteg
  split_ifs with h
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hpN : p ∈ N := h.mem_toFinset.1 hp
    by_cases hpA : p ∈ A
    · rw [Set.indicator_of_mem hpA, Set.indicator_of_mem (show p ∈ A ∩ N from ⟨hpA, hpN⟩)]
    · rw [Set.indicator_of_notMem hpA, Set.indicator_of_notMem (fun h' => hpA h'.1)]
  · rfl

theorem finPointInteg_empty (f : Obj → ℝ) (N : Set Obj) (g : Obj → X.PObj.OrTangent) :
    finPointInteg f N g ∅ = 0 := by
  unfold finPointInteg
  split_ifs
  · simp
  · rfl

/-- **On a sheet with at most one point, `finPointInteg` is E1's `pointInteg`.** -/
theorem finPointInteg_eq_pointInteg (f : Obj → ℝ) {N : Set Obj} (hN : N.Subsingleton)
    (g : Obj → X.PObj.OrTangent) (A : Set Obj) :
    finPointInteg f N g A = pointInteg f N g A := by
  classical
  rw [finPointInteg_inter]
  by_cases h : (A ∩ N).Nonempty
  · obtain ⟨p, hp⟩ := h
    have hAN : A ∩ N = (({p} : Finset Obj) : Set Obj) := by
      rw [Finset.coe_singleton]
      exact Subset.antisymm (fun y hy => hN hy.2 hp.2) (singleton_subset_iff.2 hp)
    rw [hAN, finPointInteg_coe hN.finite _ (by rw [← hAN]; exact inter_subset_right),
      Finset.sum_singleton, pointInteg_of_mem hN hp]
  · rw [not_nonempty_iff_eq_empty.1 h, finPointInteg_empty,
      pointInteg_of_empty (not_nonempty_iff_eq_empty.1 h)]

omit [ParacompactSpace Obj] in
/-- Every set is measurable in a finite set of points. -/
theorem isMeasIn_point_finite {S : Set (Set Obj)} {N : Set Obj} (hN : N.Finite) (A : Set Obj) :
    (SheetNullSets.point S).IsMeasIn N A := by
  have hB : MeasurableSet[borel Obj] (A ∩ N) := by
    have ho : IsOpen (A ∩ N)ᶜ := (hN.subset inter_subset_right).isClosed.isOpen_compl
    exact (MeasurableSpace.measurableSet_generateFrom ho : MeasurableSet[borel Obj] _).of_compl
  exact SheetNullSets.isMeasIn_inter_iff.1 (SheetNullSets.isMeasIn_of_borel hB)

/-- **The tangent space of a finite set at one of its points is that of the point.** -/
theorem submanifoldTangent_finite_eq {N : Set Obj} (hN : N.Finite) {y : Obj} (hy : y ∈ N) :
    X.PObj.submanifoldTangent N y = X.PObj.submanifoldTangent {y} y := by
  have hV : IsOpen (N \ {y})ᶜ := (hN.sdiff).isClosed.isOpen_compl
  refine MPolyfold.submanifoldTangent_congr hV (fun h => h.2 rfl) ?_
  ext z
  simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff, mem_singleton_iff, not_and, not_not]
  constructor
  · rintro ⟨hz, h⟩
    exact ⟨h hz, fun _ => h hz⟩
  · rintro ⟨rfl, -⟩
    exact ⟨hy, fun _ => rfl⟩

theorem dim_tangent_eq_zero_of_finite {N : Set Obj} (hN : N ∈ finPointSheets X) {m : ℕ}
    (o : X.PObj.SubmanifoldOrientation N m) {p : Obj} (hp : p ∈ N) : (o.tangent p).dim = 0 :=
  dim_eq_zero_of_isOrientedAt_singleton (hN.2 hp) (o.isOrientedAt_tangent hp)
    (by rw [MPolyfold.SubmanifoldOrientation.tangent_carrier, submanifoldTangent_finite_eq hN.1 hp])

variable (X) in
/-- **Integration over finite sets of oriented points**: a `SheetIntegration` in dimension `0`,
for every ep-groupoid; the forms are the invariant functions, the sheets the finite sets of
smooth points, and `∫_A f|(N, o) = ∑_{p ∈ N ∩ A} ± f(p)`. -/
def finPointIntegration :
    X.SheetIntegration (SheetNullSets.point (finPointSheets X)) (invariantFunctions X) where
  integ ω N g A := finPointInteg (ω : Obj → ℝ) N g A
  integ_add ω τ N g A := by
    unfold finPointInteg
    split_ifs with h
    · rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hpA : p ∈ A
      · rw [Set.indicator_of_mem hpA, Set.indicator_of_mem hpA, Set.indicator_of_mem hpA,
          Submodule.coe_add, Pi.add_apply, mul_add]
      · rw [Set.indicator_of_notMem hpA, Set.indicator_of_notMem hpA,
          Set.indicator_of_notMem hpA, add_zero]
    · rw [add_zero]
  integ_smul c ω N g A := by
    unfold finPointInteg
    split_ifs with h
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hpA : p ∈ A
      · rw [Set.indicator_of_mem hpA, Set.indicator_of_mem hpA, Submodule.coe_smul,
          Pi.smul_apply, smul_eq_mul]
        ring
      · rw [Set.indicator_of_notMem hpA, Set.indicator_of_notMem hpA, mul_zero]
    · rw [mul_zero]
  lindelof N hN := by
    have : Finite N := hN.1.to_subtype
    infer_instance
  inter_mem N hN V _ := ⟨hN.1.subset inter_subset_left, inter_subset_left.trans hN.2⟩
  isMeasIn_inter N hN N' _ := isMeasIn_point_finite hN.1 _
  isNull_tangent_ne N hN N' hN' := by
    refine SheetNullSets.point_isNull_iff.2 (disjoint_left.2 ?_)
    rintro y ⟨⟨hyN, hyN'⟩, hne⟩ -
    exact hne ((submanifoldTangent_finite_eq hN.1 hyN).trans
      (submanifoldTangent_finite_eq hN'.1 hyN').symm)
  isMeasIn_tangent_eq N hN N' _ _ _ _ _ := isMeasIn_point_finite hN.1 _
  integ_hasSum ω N hN m o A hA _ hd := by
    classical
    unfold finPointInteg
    rw [dif_pos hN.1]
    simp only [dif_pos hN.1]
    refine hasSum_sum fun p _ => ?_
    by_cases hp : p ∈ ⋃ k, A k
    · obtain ⟨k₀, hk₀⟩ := mem_iUnion.1 hp
      rw [Set.indicator_of_mem hp]
      have h0 : ∀ k, k ≠ k₀ →
          (A k).indicator (fun p => frameSign (o.tangent p) * (ω : Obj → ℝ) p) p = 0 :=
        fun k hk => Set.indicator_of_notMem (fun hpk => Set.disjoint_left.1 (hd hk) hpk hk₀) _
      have h1 := hasSum_single k₀ h0
      rwa [Set.indicator_of_mem hk₀] at h1
    · rw [Set.indicator_of_notMem hp]
      have h0 : ∀ k,
          (A k).indicator (fun p => frameSign (o.tangent p) * (ω : Obj → ℝ) p) p = 0 :=
        fun k => Set.indicator_of_notMem (fun hpk => hp (mem_iUnion.2 ⟨k, hpk⟩)) _
      simp only [h0]
      exact hasSum_zero
  integ_null ω N _ m o A hA hnull := by
    have hA0 : A = ∅ := (SheetNullSets.point_isNull_iff.1 hnull).eq_bot_of_le hA
    rw [hA0]
    exact finPointInteg_empty _ _ _
  integ_congr ω N hN N' hN' m m' o o' A hA _ heq := by
    have hAf : A.Finite := hN.1.subset (hA.trans inter_subset_left)
    change finPointInteg _ N _ A = finPointInteg _ N' _ A
    rw [finPointInteg_of_subset hN.1 (hA.trans inter_subset_left) hAf,
      finPointInteg_of_subset hN'.1 (hA.trans inter_subset_right) hAf]
    exact Finset.sum_congr rfl fun p hp => by rw [heq p (hAf.mem_toFinset.1 hp)]
  integ_neg ω N hN N' hN' m m' o o' A hA _ hne := by
    have hAf : A.Finite := hN.1.subset (hA.trans inter_subset_left)
    change finPointInteg _ N _ A = -finPointInteg _ N' _ A
    rw [finPointInteg_of_subset hN.1 (hA.trans inter_subset_left) hAf,
      finPointInteg_of_subset hN'.1 (hA.trans inter_subset_right) hAf, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpA := hAf.mem_toFinset.1 hp
    rw [frameSign_eq_neg (dim_tangent_eq_zero_of_finite hN o (hA hpA).1)
      (dim_tangent_eq_zero_of_finite hN' o' (hA hpA).2) (by
        rw [MPolyfold.SubmanifoldOrientation.tangent_carrier,
          MPolyfold.SubmanifoldOrientation.tangent_carrier]
        exact (hne p hpA).1) (hne p hpA).2, neg_mul]
  image_mem N hN f f' U U' hf hNU _ :=
    ⟨hN.1.image f, image_subset_iff.2 fun p hp => mem_iInter.2 fun k =>
      hf.isScSmoothOn.mapsTo_levelSet k ⟨hNU hp, mem_iInter.1 (hN.2 hp) k⟩⟩
  isMeasIn_image N hN f f' U U' hf _ _ A _ _ := isMeasIn_point_finite (hN.1.image f) _
  integ_image ω N hN m o hM f f' U U' hf hNU hmor A hA _ := by
    classical
    have hAf : A.Finite := hN.1.subset hA
    have hinj : InjOn f (hAf.toFinset : Set Obj) := fun a ha b hb hab => by
      rw [hAf.coe_toFinset] at ha hb
      rw [← hf.left_inv a (hNU (hA ha)), hab, hf.left_inv b (hNU (hA hb))]
    have hfA : f '' A = ((hAf.toFinset.image f : Finset Obj) : Set Obj) := by
      rw [Finset.coe_image, hAf.coe_toFinset]
    change finPointInteg _ (f '' N) _ (f '' A) = finPointInteg _ N _ A
    rw [hfA, finPointInteg_coe (hN.1.image f) _ (by rw [← hfA]; exact image_mono hA),
      Finset.sum_image hinj, finPointInteg_of_subset hN.1 hA hAf]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpA := hAf.mem_toFinset.1 hp
    obtain ⟨ψ, hsrc, htgt, -⟩ := hmor p (hA hpA)
    have hinv : (ω : Obj → ℝ) (f p) = (ω : Obj → ℝ) p := by
      have := ω.2 ψ
      rw [hsrc, htgt] at this
      exact this.symm
    rw [MPolyfold.SubmanifoldOrientation.mapDiffeo_tangent o hM hf hNU (hA hpA), frameSign_map,
      hinv]

theorem finPointIntegration_integ (ω : invariantFunctions X) (N : Set Obj)
    (g : Obj → X.PObj.OrTangent) (A : Set Obj) :
    (finPointIntegration X).integ ω N g A = finPointInteg (ω : Obj → ℝ) N g A := rfl

/-- The null sets of the finite sets of oriented points are those of dimension `0`. -/
theorem finPoint_isNull_iff_isHNull_zero (N B : Set Obj) :
    (SheetNullSets.point (finPointSheets X)).IsNull N B ↔ X.PObj.IsHNull 0 (B ∩ N) := by
  rw [SheetNullSets.point_isNull_iff, MPolyfold.isHNull_zero_iff,
    Set.disjoint_iff_inter_eq_empty]

end EpGroupoid

namespace EP

variable (A : EP.{u})

/-- **The integration of `0`-forms over finite sets of oriented points** (2021 §9.5 for
`n = 1`): `∫_B a|(N, o) = ∑_{p ∈ N ∩ B} ±a(p)` for `a ∈ Ω⁰_{ep,∞}(X)`, the sheets the finite sets
of smooth points (`finPointSheets`), the null sets those of dimension `0`. -/
def finZeroFormIntegration :
    A.X.SheetIntegration (SheetNullSets.point (EpGroupoid.finPointSheets A.X))
      (A.epFormsInfty 0) :=
  (EpGroupoid.finPointIntegration A.X).comap A.zeroFormEvalInv

theorem finZeroFormIntegration_integ (a : A.epFormsInfty 0) (N : Set A.Obj)
    (g : A.Obj → A.X.PObj.OrTangent) (B : Set A.Obj) :
    A.finZeroFormIntegration.integ a N g B =
      EpGroupoid.finPointInteg (A.zeroFormEval a) N g B := rfl

/-- `∫_B a|(N, o) = ∑_{p ∈ B} ±a(p)` for `B ⊆ N` finite. -/
theorem finZeroFormIntegration_integ_of_subset (a : A.epFormsInfty 0) {N : Set A.Obj}
    (hN : N.Finite) (g : A.Obj → A.X.PObj.OrTangent) {B : Set A.Obj} (hB : B ⊆ N)
    (hBf : B.Finite) :
    A.finZeroFormIntegration.integ a N g B =
      ∑ p ∈ hBf.toFinset, EpGroupoid.frameSign (g p) * A.zeroFormEval a p :=
  EpGroupoid.finPointInteg_of_subset hN hB hBf

/-- **On sheets with at most one point the two integrations of `0`-forms agree.** -/
theorem finZeroFormIntegration_integ_eq (a : A.epFormsInfty 0) {N : Set A.Obj}
    (hN : N.Subsingleton) (g : A.Obj → A.X.PObj.OrTangent) (B : Set A.Obj) :
    A.finZeroFormIntegration.integ a N g B = A.zeroFormIntegration.integ a N g B :=
  EpGroupoid.finPointInteg_eq_pointInteg _ hN g B

end EP

end Polyfold
