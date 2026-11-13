import Polyfold.Chapter9.MultiChartIntegration
import Polyfold.Chapter9.IntegralCovering

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, Theorem 9.5.4 (p. 438), gap G.107.  Numbers and pages are the 2021
text's.

# Compact sheets lie in the class `F.msheets`

A nonempty compact `n`-dimensional submanifold `N` is covered by finitely many open sets `V`
with `N ∩ V ∈ F.sheets` (`exists_mem_sheets`); listed as a sequence which repeats one of them,
all but finitely many pieces are empty, so `∑ₖ ∫_{P k} |ω|` is a finite sum
(`msheets_of_isCompact`).  This needs no one-chart condition: e.g. the whole circle `S¹ ⊆ ℝ²`
(`CircleOneSheet.lean`).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {n : ℕ} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω] {F : X.FormEval n Ω}

namespace FormEval

/-- **A nonempty compact `n`-dimensional submanifold is a sheet of the class `F.msheets`**:
it has a finite cover by one-chart sheets, and `∫ |ω|` over it is finite. -/
theorem msheets_of_isCompact {N : Set Obj} (hN : X.PObj.IsSubmanifoldOfDim N n)
    (hc : IsCompact N) (hne : N.Nonempty) : N ∈ F.msheets := by
  classical
  choose Vf hVo hxV hVs using fun y : N => exists_mem_sheets (F := F) hN y.2
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover Vf hVo fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, hxV _⟩
  obtain ⟨x₀, hx₀⟩ := hne
  set l : List N := (insert ⟨x₀, hx₀⟩ t).toList with hl
  have hmem0 : (⟨x₀, hx₀⟩ : N) ∈ l := by rw [hl, Finset.mem_toList]; exact Finset.mem_insert_self _ _
  obtain ⟨i₀, hi₀, hli₀⟩ := List.mem_iff_getElem.1 hmem0
  let D : F.ChartCover N :=
    { V := fun k => Vf (l.getD k ⟨x₀, hx₀⟩)
      isOpen := fun k => hVo _
      cover := fun y hy => by
        obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 (ht hy)
        have hil : i ∈ l := by rw [hl, Finset.mem_toList]; exact Finset.mem_insert_of_mem hi
        obtain ⟨j, hj, hlj⟩ := List.mem_iff_getElem.1 hil
        refine mem_iUnion.2 ⟨j, ?_⟩
        rw [List.getD_eq_getElem _ _ hj, hlj]
        exact hyi
      mem := fun k => hVs _ }
  refine ⟨hN, D, fun ω => summable_of_ne_finset_zero (s := Finset.range l.length) fun k hk => ?_⟩
  have hk' : l.length ≤ k := by simpa using hk
  have hP : D.P k = ∅ := by
    refine eq_empty_of_forall_notMem fun y hy => ?_
    have hyk : y ∈ Vf (l.getD k ⟨x₀, hx₀⟩) := hy.2.1
    rw [List.getD_eq_default _ _ hk'] at hyk
    refine hy.2.2 i₀ (lt_of_lt_of_le hi₀ hk') ?_
    change y ∈ Vf (l.getD i₀ ⟨x₀, hx₀⟩)
    rw [List.getD_eq_getElem _ _ hi₀, hli₀]
    exact hyk
  unfold chartAbs
  rw [hP, empty_inter, image_empty, Measure.restrict_empty, integral_zero_measure]

end FormEval

end EpGroupoid

end Polyfold
