import Polyfold.Chapter3.TameGerms
import Polyfold.Chapter3.GoodPositionGermG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, Definitions 3.14,
3.50, 3.51 and 3.53 in a tame chart, **in the text's germ reading** (phase 2 of the germ-versus-chart
work; Findings, Chapter 3, items 260–299).

# sc-Fredholm sections and tame germ data, germ reading

## The text, paraphrased

(Definition 3.14) An sc-Fredholm section is sc-smooth, regularizing, and an sc-Fredholm germ
(Definition 3.11) at every smooth point.  (Definitions 3.50, 3.51) For a tame strong bundle the
germ data are taken in a tame chart.  (Definition 3.53) An sc-Fredholm germ in good position.
The germs of Definition 3.11 are those of Definitions 3.1–3.2, with levels that may shrink.

## What is formalized

* `Polyfold.StrongBundle.IsScFredholmSection`: Definition 3.14 with the germ reading
  `IsScFredholmGerm` of Definition 3.11.
* `Polyfold.StrongBundle.IsScFredholmGermTame`, `Polyfold.StrongBundle.IsGoodPositionGermTame`:
  Definitions 3.50 and 3.53 in a tame chart (`IsTameChart`), germ reading.
* `Polyfold.StrongBundle.IsScFredholmSectionTame`: Definition 3.51, germ reading.
* The project's whole-chart notions imply these (`…isScFredholmSection`, `…isScFredholmGermTame`,
  `…isGoodPositionGermTame`, `…isScFredholmSectionTame`), and tame germ data are germ data.

## What the text leaves implicit, and the choices made

As in `IsScFredholmGerm` (`Chapter3/GermFillingChart.lean`): the filling and the sc⁺-section are
germs, the strong bundle isomorphism and the basic germ are as in `IsConjugateToBasicGerm`.
These notions are the targets of the redefinition of Definition 3.11 in phase 2.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

namespace StrongBundle

variable (B) in
/-- **Definition 3.14** (with the text's germ reading of Definition 3.11): `f` is sc-smooth,
regularizing, and an sc-Fredholm germ (`IsScFredholmGerm`) at every smooth point.  (The project's
original whole-chart reading is `IsScFredholmSectionWholeChart`, `StrongBundleSections.lean`.) -/
structure IsScFredholmSection (f : X → Y) : Prop where
  isScSmooth : B.IsScSmoothSection f
  regularizing : ∀ m, ∀ x ∈ PX.levelSet m, f x ∈ B.doubleLevel m (m + 1) → x ∈ PX.levelSet (m + 1)
  germ : ∀ x ∈ PX.smoothSet, B.IsScFredholmGerm f x

/-- **Project ⇒ germ reading** for Definition 3.14. -/
theorem IsScFredholmSectionWholeChart.isScFredholmSection (h : B.IsScFredholmSectionWholeChart f) :
    B.IsScFredholmSection f :=
  ⟨h.isScSmooth, h.regularizing, fun x hx => (h.germ x hx).isScFredholmGerm⟩

/-- A zero of a regularizing section is a smooth point (germ reading, phase 2; the germ form of
`IsScFredholmSectionWholeChart.mem_smoothSet_of_isZeroAt`, used by Chapter 5). -/
theorem IsScFredholmSection.mem_smoothSet_of_isZeroAt
    (hf : B.IsScFredholmSection f) {x : X} (hx : IsZeroAt P f x) : x ∈ PX.smoothSet := by
  refine mem_iInter.2 fun m => ?_
  induction m with
  | zero => rw [PX.levelSet_zero]; exact mem_univ _
  | succ m ih =>
    refine hf.regularizing m x ih ?_
    rw [hx]; exact B.fiberZero_mem_doubleLevel ih

variable (B) in
/-- **Definition 3.50** (the text's germ reading): the data of `IsScFredholmGerm` in a tame strong
bundle chart (`IsTameChart`).  (Whole-chart reading: `IsScFredholmGermTameWholeChart`.) -/
def IsScFredholmGermTame (f : X → Y) (x₀ : X) : Prop :=
  x₀ ∈ PX.smoothSet ∧
  ∃ (c : StrongBundleChart PX P) (_ : B.IsTameChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
    (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0) (s : c.φ.model.E 0 → c.F 1),
    IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g ∧
    IsScPlusGerm c.φ.model.C c.U s ∧ c.F.toBase 1 (s 0) = g 0 ∧
    IsConjugateToBasicGerm c.U (fun u => g u - c.F.toBase 1 (s u))

/-- Tame germ data are germ data (Definition 3.50 ⟹ Definition 3.11, germ reading). -/
theorem IsScFredholmGermTame.isScFredholmGerm {x : X} (h : B.IsScFredholmGermTame f x) :
    B.IsScFredholmGerm f x := by
  obtain ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj⟩ := h
  exact ⟨hs, c, hc.1, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj⟩

/-- **Project ⇒ germ reading** for Definition 3.50. -/
theorem IsScFredholmGermTameWholeChart.isScFredholmGermTame {x : X} (h : B.IsScFredholmGermTameWholeChart f x) :
    B.IsScFredholmGermTame f x := by
  obtain ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj⟩ := h
  exact ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill.isFillingGerm c.relOpen c.isRetraction h0,
    ⟨ScNbhdGerm.ofSet c.relOpen.relOpen h0, fun _ hu => hu,
      hsm.isScSmoothGerm c.isQuadrantLike c.relOpen.relOpen h0⟩, hs0, hconj⟩

variable (B) in
/-- **Definition 3.53 in a tame chart** (the text's germ reading): the data of
`IsGoodPositionGerm` in a tame strong bundle chart.  (Whole-chart reading:
`IsGoodPositionGermTameWholeChart`.) -/
def IsGoodPositionGermTame (f : X → Y) (x₀ : X) : Prop :=
  x₀ ∈ PX.smoothSet ∧
  ∃ (c : StrongBundleChart PX P) (_ : B.IsTameChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
    (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0) (s : c.φ.model.E 0 → c.F 1),
    IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g ∧
    IsScPlusGerm c.φ.model.C c.U s ∧ c.F.toBase 1 (s 0) = g 0 ∧
    IsConjugateToBasicGerm c.U (fun u => g u - c.F.toBase 1 (s u)) ∧
    ∃ (G : ScNbhdGerm c.φ.model.E c.φ.model.C) (Dg : c.φ.model.E 1 → c.φ.model.E 0 →L[ℝ] c.F 0),
      G.U 0 ⊆ c.U ∧ IsSc1GermWith G g Dg ∧
      IsGoodPositionAtGerm c.relOpen c.isRetraction h0 (Dg 0)

/-- A tame germ in good position is a germ in good position (germ reading). -/
theorem IsGoodPositionGermTame.isGoodPositionGerm {x : X} (h : B.IsGoodPositionGermTame f x) :
    B.IsGoodPositionGerm f x := by
  obtain ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj, hgp⟩ := h
  exact ⟨hs, c, hc.1, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj, hgp⟩

/-- A tame germ in good position is a tame sc-Fredholm germ (germ reading). -/
theorem IsGoodPositionGermTame.isScFredholmGermTame {x : X}
    (h : B.IsGoodPositionGermTame f x) : B.IsScFredholmGermTame f x := by
  obtain ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj, -⟩ := h
  exact ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj⟩

/-- **Project ⇒ germ reading** for Definition 3.53 in a tame chart. -/
theorem IsGoodPositionGermTameWholeChart.isGoodPositionGermTame {x : X}
    (h : B.IsGoodPositionGermTameWholeChart f x) : B.IsGoodPositionGermTame f x := by
  obtain ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj, hgp⟩ := h
  exact ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill.isFillingGerm c.relOpen c.isRetraction h0,
    ⟨ScNbhdGerm.ofSet c.relOpen.relOpen h0, fun _ hu => hu,
      hsm.isScSmoothGerm c.isQuadrantLike c.relOpen.relOpen h0⟩, hs0, hconj,
    ScNbhdGerm.ofSet c.relOpen.relOpen h0, scDeriv c.U g, fun _ hu => hu,
    hfill.isScSmooth.isSc1.isSc1GermWith_ofSet c.relOpen.relOpen h0,
    isGoodPositionAt_iff_germ.1 hgp⟩

variable (B) in
/-- **Definition 3.51** (the text's germ reading): an sc-Fredholm section (`IsScFredholmSection`)
whose germ data at every smooth point can be taken in a tame chart.  (Whole-chart reading:
`IsScFredholmSectionTameWholeChart`.) -/
structure IsScFredholmSectionTame (f : X → Y) : Prop extends B.IsScFredholmSection f where
  germTame : ∀ x ∈ PX.smoothSet, B.IsScFredholmGermTame f x

/-- **Project ⇒ germ reading** for Definition 3.51. -/
theorem IsScFredholmSectionTameWholeChart.isScFredholmSectionTame (h : B.IsScFredholmSectionTameWholeChart f) :
    B.IsScFredholmSectionTame f :=
  { h.toIsScFredholmSectionWholeChart.isScFredholmSection with
    germTame := fun x hx => (h.germTame x hx).isScFredholmGermTame }

end StrongBundle

end Polyfold
