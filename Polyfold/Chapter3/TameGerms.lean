import Polyfold.Chapter3.LinearizationCharts

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1 and §3.6:
**sc-Fredholm germs and sections of a tame strong bundle** — Definitions 3.50 and 3.51 (the recall
of Definitions 3.11 and 3.14 at the start of §3.6) and Definition 3.53 in a **tame** strong bundle
chart, the hypotheses under which the implicit function theorems of §3.6 are proved.

# Tame strong bundle charts and tame germ data

## The text, paraphrased

(Before Definition 2.51) "A tame strong bundle retraction is one for which the retraction `r` is
tame."  (Definition 3.50, the recall of Definition 3.11 in §3.6) Let `f` be an sc-smooth section of
the tame strong bundle `P : Y → X` and `x` a smooth point.  `(f, x)` is an sc-Fredholm germ if there
is a strong bundle chart `Φ : P⁻¹(V) → K` around `x` covering `ϕ : (V, x) → (O, 0)`, **where
`K → O` is a tame strong local bundle**, such that `Φ ∘ f ∘ ϕ⁻¹` has a filling `g` near `0` and a
local sc⁺-section `s` with `s(0) = g(0)` and `g − s` conjugated near `0` to a basic germ.
(Definition 3.51) A regularizing sc-smooth section of the tame strong bundle is sc-Fredholm if
`(f, x)` is an sc-Fredholm germ at every smooth point.  (Proof of Proposition 3.52) "Since `(f, x)`
is a sc-Fredholm germ, there exists a tame strong bundle chart `Φ` around `x` such that …".
(Definition 3.53) An sc-Fredholm germ `(f, x)` of a tame strong bundle with `f(x) = 0` is in good
position if `f'(x)` is onto and `ker f'(x)` is in good position to the partial cone `C_xX`.

## What is formalized

* `StrongBundle.IsTameChart B c`: a strong bundle chart compatible with the atlas of `B`
  (`B.IsChart c`) whose base retraction `r : U → U` is tame (Definition 2.34), i.e. whose local
  strong bundle retract `K → O` is a tame strong local bundle.
* `StrongBundle.IsScFredholmGermTameWholeChart B f x`: **Definition 3.50**, the data of Definition 3.11
  (`IsScFredholmGermWholeChart`: a centred chart, a filled version `g`, an sc⁺-section `s`, `g − s`
  conjugated to a basic germ) in a tame chart; `StrongBundle.IsGoodPositionGermTameWholeChart B f x`:
  **Definition 3.53** (`IsGoodPositionGermWholeChart`) in a tame chart; `StrongBundle.IsScFredholmSectionTameWholeChart
  B f`: **Definition 3.51** (Definition 3.14 for a tame strong bundle), an sc-Fredholm section
  (`IsScFredholmSectionWholeChart`) with tame germ data at every smooth point.  The forgetful lemmas
  `IsTameChart.isChart`, `IsScFredholmGermTameWholeChart.isScFredholmGerm`,
  `IsGoodPositionGermTameWholeChart.isGoodPositionGerm`, `IsGoodPositionGermTameWholeChart.isScFredholmGermTame`,
  and `IsScFredholmSectionTameWholeChart.toIsScFredholmSectionWholeChart` (the parent structure).
* `StrongBundle.IsGoodPositionGermWholeChart.toTame`: **good position can be read in any chart of the
  germ data**: if `(f, y)` is in good position (in some chart) and has tame germ data, it is in
  good position in the tame chart (`isGoodPositionAt_of_chart_dense`, the chart independence of
  the linearization).  This is how the conclusions "every nearby zero is in good position" of
  Theorem 3.54 (1) are obtained in tame charts.
* `StrongBundle.IsScFredholmGermTameWholeChart.sectionAdd`, `Polyfold.theorem_3_15_tame_wholeChart`: **Theorem 3.15
  for tame germ data** (the proof of Theorem 3.15 does not change the chart).
* `ScRetraction.IsTame.congr` (tameness depends only on the domain and the map on it) and
  `StrongBundle.isTameChart_of_eqOn_id`: a compatible chart whose base retraction is the identity of
  `U` (`O = U` relatively open in the quadrant) is tame (`ScRetraction.id_isTame`), so the
  hypotheses are satisfiable.

## What the text leaves implicit, and the choices made (the findings)

* **Which charts are tame.**  The §3.6 theorems were first formalized with the hypothesis that the
  base retraction of *every* strong bundle chart compatible with the atlas is tame (`htame`).
  That hypothesis is false for every strong bundle over a nonempty base: compatibility constrains
  only the transition maps between the retracts `K`, so a chart `(φ, U, R, Φ)` can be replaced by
  `φ' = (1, φ)` with model `ℝ ⊕ E`, quadrant `[0, ∞) × C`, `U' = [0, ∞) × U`, base retraction
  `r'(a, u) = (1, r(u))` and `Φ' = (1, Φ)`, which is compatible with every chart `c` is and has
  `d(0, u) = 1 + d_C(u) ≠ d_C(u) = d(r'(0, u))` for `u ∈ O` (Findings, Chapter 3 items 190–199;
  the non-tameness of `r'` is `ScRetraction.halfLineConst_prod_not_isTame`, `TameVacuity.lean`,
  the compatibility of the chart is not formalized).  The text
  needs tameness only for the chart of the germ data (Definition 3.50: "where `K → O` is a tame
  strong local bundle"; proof of Proposition 3.52: "there exists a tame strong bundle chart"),
  which is what `IsScFredholmGermTameWholeChart` and `IsGoodPositionGermTameWholeChart` state.
* **Definition 3.11** itself (the first statement, for a strong bundle over a tame M-polyfold)
  does not ask for a tame chart; `IsScFredholmGermWholeChart` keeps that form, and Theorems 3.12, 3.15,
  3.18, Proposition 3.52 and the chart independence of the linearization do not need tameness.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

/-! ### Tameness depends only on the domain and the map on it -/

section Congr

variable {E : ScBanach} {C : Set (E 0)}

/-- **A retraction agreeing on its domain with a tame retraction is tame**: Definition 2.34 refers
to `r` only through its values on `U`, the retract `r(U)` and the derivatives `Dr(x)` at points of
`U` (determined by the values on the relatively open `U`, `scDeriv_eq_of_eqOn_relOpen`). -/
theorem ScRetraction.IsTame.congr {R R' : ScRetraction E C} (hR : R.IsTame) (hU : R.U = R'.U)
    (h : EqOn R R' R.U) : R'.IsTame := by
  intro n W T hT
  have hRT := hR n W T hT
  have hret : R.retract = R'.retract := by
    unfold ScRetraction.retract
    rw [← hU]
    exact h.image_eq
  refine ⟨fun x hx => ?_, fun x hx hs => ?_⟩
  · have hxR : x ∈ R.U := by rw [hU]; exact hx
    rw [← h hxR]
    exact hRT.degIndex_apply x hxR
  · have hx' : x ∈ E.lvlSet R.retract 1 := by rw [hret]; exact hx
    obtain ⟨A, hA, hAE⟩ := hRT.exists_complement x hx' hs
    refine ⟨A, ?_, hAE⟩
    have hD : scDeriv R'.U R' x = scDeriv R.U R x :=
      scDeriv_eq_of_eqOn_relOpen R.relOpen R'.isScSmooth.isSc1 R.isScSmooth.isSc1
        (by rw [hU]) subset_rfl h.symm (R.lvlSet_retract_subset 1 hx')
    rw [hD]
    exact hA

end Congr

/-! ### Tame strong bundle charts and tame germ data -/

section Bundle

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f s : X → Y}

open StrongRetr

namespace StrongBundle

variable (B) in
/-- **A tame strong bundle chart** of `P`: a strong bundle chart compatible with the atlas of `B`
whose base retraction `r : U → U` is tame (Definition 2.34), i.e. whose local strong bundle
`K → O` is a tame strong local bundle (the text before Definition 2.51: "a tame strong bundle
retraction is one for which the retraction `r` is tame"). -/
def IsTameChart (c : StrongBundleChart PX P) : Prop :=
  B.IsChart c ∧ (c.isRetraction.baseRetraction c.relOpen).IsTame

lemma IsTameChart.isChart {c : StrongBundleChart PX P} (h : B.IsTameChart c) : B.IsChart c := h.1

lemma IsTameChart.isTame {c : StrongBundleChart PX P} (h : B.IsTameChart c) :
    (c.isRetraction.baseRetraction c.relOpen).IsTame := h.2

variable (B) in
/-- **Definition 3.50** (the recall of Definition 3.11 in §3.6, for a tame strong bundle): `(f, x₀)` is
an **sc-Fredholm germ in a tame chart**: the data of Definition 3.11 (`IsScFredholmGermWholeChart`:
a strong bundle chart centred at `x₀`, a filled version `g` of `f̂`, a local sc⁺-section `s` with
`s(0) = g(0)` and `g − s` conjugated to a basic germ) in a strong bundle chart whose local strong
bundle `K → O` is tame (`IsTameChart`). This is the project's original whole-chart reading, stricter
than the text (Findings, Chapter 3, items 220–221, 260–266); the text's germ reading is
`IsScFredholmGermTame` (`TameGermsG.lean`, phase 2, items 270–330). -/
def IsScFredholmGermTameWholeChart (f : X → Y) (x₀ : X) : Prop :=
  x₀ ∈ PX.smoothSet ∧
  ∃ (c : StrongBundleChart PX P) (_ : B.IsTameChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
    (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0) (s : c.φ.model.E 0 → c.F 1),
    IsFilledVersion c.relOpen c.isRetraction h0 (c.principal f) g ∧
    IsScSmooth (F := c.F.shift) c.U s ∧ c.F.toBase 1 (s 0) = g 0 ∧
    IsConjugateToBasicGerm c.U (fun u => g u - c.F.toBase 1 (s u))

variable (B) in
/-- **Definition 3.53 in a tame chart**: `(f, x₀)` is an sc-Fredholm germ in good position, with the
data of Definition 3.53 (`IsGoodPositionGermWholeChart`) in a tame strong bundle chart
(`IsTameChart`, Definition 3.50). This is the project's original whole-chart reading, stricter than
the text (Findings, Chapter 3, items 220–221, 260–266); the text's germ reading is
`IsGoodPositionGermTame` (`TameGermsG.lean`, phase 2, items 270–330). -/
def IsGoodPositionGermTameWholeChart (f : X → Y) (x₀ : X) : Prop :=
  x₀ ∈ PX.smoothSet ∧
  ∃ (c : StrongBundleChart PX P) (_ : B.IsTameChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
    (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0) (s : c.φ.model.E 0 → c.F 1),
    IsFilledVersion c.relOpen c.isRetraction h0 (c.principal f) g ∧
    IsScSmooth (F := c.F.shift) c.U s ∧ c.F.toBase 1 (s 0) = g 0 ∧
    IsConjugateToBasicGerm c.U (fun u => g u - c.F.toBase 1 (s u)) ∧
    IsGoodPositionAt c.relOpen c.isRetraction h0 g

variable (B) in
/-- **Definition 3.51** (Definition 3.14 for a tame strong bundle): an sc-Fredholm section
(`IsScFredholmSectionWholeChart`: sc-smooth, regularizing, an sc-Fredholm germ at every smooth
point) whose germ data at every smooth point can be taken in a tame chart
(`IsScFredholmGermTameWholeChart`). This is the project's original whole-chart reading, stricter
than the text (Findings, Chapter 3, items 220–221, 260–266); the text's germ reading is
`IsScFredholmSectionTame` (`TameGermsG.lean`, phase 2, items 270–330). -/
structure IsScFredholmSectionTameWholeChart (f : X → Y) : Prop extends B.IsScFredholmSectionWholeChart f where
  germTame : ∀ x ∈ PX.smoothSet, B.IsScFredholmGermTameWholeChart f x

/-- Tame germ data are germ data (Definition 3.50 ⟹ Definition 3.11). -/
theorem IsScFredholmGermTameWholeChart.isScFredholmGerm {x : X} (h : B.IsScFredholmGermTameWholeChart f x) :
    B.IsScFredholmGermWholeChart f x := by
  obtain ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj⟩ := h
  exact ⟨hs, c, hc.1, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj⟩

/-- Good position in a tame chart is good position. -/
theorem IsGoodPositionGermTameWholeChart.isGoodPositionGerm {x : X} (h : B.IsGoodPositionGermTameWholeChart f x) :
    B.IsGoodPositionGermWholeChart f x := by
  obtain ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj, hgp⟩ := h
  exact ⟨hs, c, hc.1, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj, hgp⟩

/-- A germ in good position in a tame chart has tame germ data. -/
theorem IsGoodPositionGermTameWholeChart.isScFredholmGermTame {x : X} (h : B.IsGoodPositionGermTameWholeChart f x) :
    B.IsScFredholmGermTameWholeChart f x := by
  obtain ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj, -⟩ := h
  exact ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj⟩

/-- **Good position in any chart of the germ data** (the chart independence of Definition 3.53):
if `(f, y)`, `f(y) = 0`, is in good position in some chart (`IsGoodPositionGermWholeChart`) and has germ data
in a tame chart (`IsScFredholmGermTameWholeChart`), then it is in good position in that tame chart.  In the
chart `c₁` of the good position, `Tf̃₁(0)` is onto `K₀ ⊇ ρ(0)F_∞` and `ker Dg₁(0) ⊆ T₀O` is in good
position to `C = C_0` inside `T₀O`; `isGoodPositionAt_of_chart_dense` carries both to the tame
chart. -/
theorem IsGoodPositionGermWholeChart.toTame (hf : B.IsScSmoothSection f) {y : X}
    (hg : B.IsGoodPositionGermWholeChart f y) (hy : B.IsScFredholmGermTameWholeChart f y) (hy0 : IsZeroAt P f y) :
    B.IsGoodPositionGermTameWholeChart f y := by
  obtain ⟨-, c₁, hc₁, hyV₁, hφ0₁, h0U₁, g₁, s₁, hfill₁, -, -, -, hgp₁⟩ := hg
  obtain ⟨hys, c, hct, hyV, hφ0, h0U, g, s, hfill, hs, hs0, hconj⟩ := hy
  obtain ⟨n, Wq, T, hT⟩ := c₁.φ.model.isPartialQuadrant
  have hz : c₁.φ.model.E.toBase 1 (0 : c₁.φ.model.E 1) = c₁.φ y := by rw [map_zero, hφ0₁]
  refine ⟨hys, c, hct, hyV, hφ0, h0U, g, s, hfill, hs, hs0, hconj, ?_⟩
  refine StrongBundle.isGoodPositionAt_of_chart_dense hf hy0 hc₁ hyV₁ hz
    hfill₁.isScSmooth.isSc1 ?_ T hT ?_ ?_ hct.1 hyV hφ0 h0U hfill hs hs0 hconj
  · -- `f̂ = g₁` on `O` near `φ₁(y) = 0`
    have h1 := hfill₁.filler.eq_on
    rw [c₁.r_image] at h1
    rw [hφ0₁]
    exact h1
  · -- `ρ(0)F_∞ ⊆ K₀ = Tf̃₁(0)(T₀O)`
    intro k _
    have hk : ρ c₁.R (c₁.φ y) k ∈ rangeS (ρCLM c₁.isRetraction h0U₁) := by
      rw [hφ0₁]; exact ⟨k, rfl⟩
    exact hgp₁.surj _ hk
  · -- the kernel condition at `0`, where `C_0 = C` and `ker Dg₁(0) ⊆ T₀O`
    rw [hφ0₁, partialQuadrantAtWith_zero, ← hT, inf_eq_left.2 hgp₁.kernel.le]
    exact hgp₁.kernel

/-- **Theorem 3.15, the germ property, in a tame chart**: if `(f, x)` has germ data in a tame chart
and `s` is an sc⁺-section, then `(f + s, x)` has germ data in the same tame chart (the proof of
`IsScFredholmGermWholeChart.sectionAdd`: filled version `g + ŝ ∘ r`, sc⁺-section `ŝ₁ ∘ r + t₀`, Lemma
3.17). -/
theorem IsScFredholmGermTameWholeChart.sectionAdd {x : X} (hfs : IsSection P f)
    (hg : B.IsScFredholmGermTameWholeChart f x) (hs : B.IsScPlusSection s) :
    B.IsScFredholmGermTameWholeChart (Polyfold.sectionAdd P f s) x := by
  obtain ⟨hxs, c, hct, hxV, h0, h0U, g, t₀, hfill, ht₀, ht₀0, hconj⟩ := hg
  have hc := hct.1
  have hU := c.relOpen.isScDomain
  -- `ŝ₁ ∘ r` is sc-smooth into `F¹` on `U`, and `ŝ ∘ r = ι ∘ ŝ₁ ∘ r`
  have hlift : IsScSmooth (F := c.F.shift) c.U fun u => c.principalLift s (StrongRetr.r c.R u) :=
    (((hs.isScSmoothRetractMap_one hc).comp_isScSmooth (c.isRetraction.baseRetraction c.relOpen)
      c.base_retract).snd hU).congr hU
      fun _ _ => rfl
  have hsr : IsScSmooth c.U fun u => c.principal s (StrongRetr.r c.R u) :=
    (hlift.toBase_shift hU).congr hU fun u hu => hs.toBase_principalLift hc (c.r_mem_O hu)
  refine ⟨hxs, c, hct, hxV, h0, h0U, fun u => g u + c.principal s (StrongRetr.r c.R u),
    fun u => c.principalLift s (StrongRetr.r c.R u) + t₀ u, ⟨hfill.isScSmooth.add hU hsr, ?_⟩,
    hlift.add hU ht₀, ?_, ?_⟩
  · -- Lemma 3.17
    have h17 := lemma_3_17 c.relOpen c.isRetraction h0U hfill.filler
      (s := c.principal s) fun z hz => hs.mem_K hc (c.r_image ▸ hz)
    refine h17.congr_left c.relOpen c.isRetraction h0U fun z hz => ?_
    exact (c.principal_sectionAdd hfs hs.1 (c.r_image ▸ hz)).symm
  · -- the value at `0`
    simp only [map_add, ht₀0]
    rw [hs.toBase_principalLift hc (c.r_mem_O h0U), add_comm]
  · -- `(g + t̃) − (t̃ + t₀) = g − t₀` on `U`
    refine hconj.congr fun u hu => ?_
    simp only [map_add]
    rw [hs.toBase_principalLift hc (c.r_mem_O hu)]
    abel

/-- **A compatible chart whose base retraction is the identity of `U` is tame** (the hypotheses
`IsTameChart`, `IsScFredholmGermTameWholeChart` are satisfiable): if `r(u) = u` on `U` (the retract `O = U`
is relatively open in the partial quadrant), the base retraction agrees on `U` with the identity
retraction, which is tame (`ScRetraction.id_isTame`). -/
theorem isTameChart_of_eqOn_id {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (hid : ∀ u ∈ c.U, StrongRetr.r c.R u = u) : B.IsTameChart c :=
  ⟨hc, (ScRetraction.id_isTame c.relOpen).congr rfl fun u hu => (hid u hu).symm⟩

end StrongBundle

/-- **Theorem 3.15 for a tame strong bundle** (stability under sc⁺-perturbations, Definition
3.51): if `f` is an sc-Fredholm section with tame germ data and `s` is an sc⁺-section, then `f + s`
is an sc-Fredholm section with tame germ data (Theorem 3.15, `theorem_3_15_wholeChart`, and the germ data in
the same tame chart, `IsScFredholmGermTameWholeChart.sectionAdd`). -/
theorem theorem_3_15_tame_wholeChart (hf : B.IsScFredholmSectionTameWholeChart f) (hs : B.IsScPlusSection s) :
    B.IsScFredholmSectionTameWholeChart (sectionAdd P f s) where
  toIsScFredholmSectionWholeChart := theorem_3_15_wholeChart hf.toIsScFredholmSectionWholeChart hs
  germTame x hx := (hf.germTame x hx).sectionAdd hf.isScSmooth.1 hs

end Bundle

end Polyfold
