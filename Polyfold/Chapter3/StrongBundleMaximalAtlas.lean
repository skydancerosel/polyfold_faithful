import Polyfold.Chapter2.StrongBundleRestrict
import Polyfold.Chapter3.StrongBundleSections

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §2.5,
Definitions 2.50–2.51: the strong bundle charts of a strong bundle (the maximal atlas of its
equivalence class), and their restrictions.

# The maximal strong bundle atlas

## The text, paraphrased

(Definition 2.51) A strong bundle is `P : Y → X` with an equivalence class of strong bundle
atlases; the later sections speak of "a strong bundle chart of `P`" (Definitions 3.3, 3.6, 3.11,
Lemma 5.2, ...), i.e. a chart of some atlas of the class.

## What is formalized

* `Polyfold.StrongBundle.IsChart.compatible`: **two strong bundle charts of `P` are compatible**
  (by the locality of compatibility, `StrongBundleChart.compatible_of_locally`).
* `StrongBundle.maximalAtlas` (all strong bundle charts of `P`, an atlas equivalent to the given
  one, `maximalAtlas_equiv`), `StrongBundle.isChart_iff_exists_equiv` (**a chart of `P` is a chart
  of some atlas of the equivalence class**) and `StrongBundle.isChart_congr` (**the charts of `P`
  depend only on the equivalence class of the atlas**; the analogue of `MPolyfold.isChart_congr`).
* `StrongBundle.IsChart.restrict`: **the restriction of a strong bundle chart of `P` to an open
  subset of the domain of its base chart is a strong bundle chart of `P`**
  (`StrongBundleChart.restrict`, `StrongBundleChart.Compatible.restrict_left`).

## What the text leaves implicit, and the choices made

* `StrongBundle.IsChart` (`StrongBundleSections.lean`) is "compatible with the charts of the given
  atlas".  That this is the union of the atlases of the equivalence class needs the locality of
  compatibility (`isChart_iff_exists_equiv`); the text does not discuss it.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

namespace StrongBundle

variable {B : StrongBundle PX P}

/-- **Two strong bundle charts of `P` are compatible** (both are compatible with the charts of the
atlas, which cover `Y`; `StrongBundleChart.compatible_of_locally`).  The analogue of
`MPolyfold.IsChart.compatible`; implicit in Definition 2.51 (round-trip item V2.58). -/
theorem IsChart.compatible {c c' : StrongBundleChart PX P} (hc : B.IsChart c)
    (hc' : B.IsChart c') : c.Compatible c' :=
  StrongBundleChart.compatible_of_locally c c' B.atlas.charts hc (fun χ hχ => (hc' χ hχ).symm)
    fun y _ => B.atlas.cover y

/-- **The restriction of a strong bundle chart of `P`** to an open subset `s` of the domain of its
base chart is a strong bundle chart of `P` (round-trip items V5.4, V2.58). -/
theorem IsChart.restrict {c : StrongBundleChart PX P} (hc : B.IsChart c) {s : Set X}
    (hs : s ⊆ c.φ.source) (hso : IsOpen s) : B.IsChart (c.restrict hs hso) :=
  fun c' hc' => (hc c' hc').restrict_left hs hso

variable (B) in
/-- **The maximal strong bundle atlas** of `P`: all strong bundle charts of `P` (pairwise compatible
by `IsChart.compatible`). -/
def maximalAtlas : StrongBundleAtlas PX P where
  charts := {c | B.IsChart c}
  compatible _ hc _ hc' := IsChart.compatible hc hc'
  cover y := by
    obtain ⟨c, hc, hy⟩ := B.atlas.cover y
    exact ⟨c, B.isChart_of_mem hc, hy⟩

variable (B) in
/-- The maximal atlas belongs to the equivalence class of the atlas of `B` (Definition 2.51). -/
theorem maximalAtlas_equiv : B.maximalAtlas.Equiv B.atlas :=
  (StrongBundleAtlas.equiv_iff _ _).2 fun _ hc c' hc' => hc c' hc'

/-- **The strong bundle charts of `P` are the charts of the atlases of the equivalence class**
(Definition 2.51's "equivalence class of strong bundle atlases", read through its maximal atlas;
round-trip item V2.58). -/
theorem isChart_iff_exists_equiv (c : StrongBundleChart PX P) :
    B.IsChart c ↔ ∃ A : StrongBundleAtlas PX P, A.Equiv B.atlas ∧ c ∈ A.charts := by
  constructor
  · intro hc
    exact ⟨B.maximalAtlas, B.maximalAtlas_equiv, hc⟩
  · rintro ⟨A, hA, hcA⟩ c' hc'
    exact (StrongBundleAtlas.equiv_iff A B.atlas).1 hA c hcA c' hc'

/-- **The strong bundle charts of `P` depend only on the equivalence class of the atlas** (the
analogue of `MPolyfold.isChart_congr`; Definition 2.51, round-trip item V2.58). -/
theorem isChart_congr {B B' : StrongBundle PX P} (h : B.atlas.Equiv B'.atlas)
    (c : StrongBundleChart PX P) : B.IsChart c ↔ B'.IsChart c := by
  rw [isChart_iff_exists_equiv, isChart_iff_exists_equiv]
  constructor
  · rintro ⟨A, hA, hcA⟩
    exact ⟨A, hA.trans h, hcA⟩
  · rintro ⟨A, hA, hcA⟩
    exact ⟨A, hA.trans h.symm, hcA⟩

end StrongBundle

end Polyfold
