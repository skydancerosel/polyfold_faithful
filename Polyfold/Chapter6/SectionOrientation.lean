import Polyfold.Chapter6.ContinuousOrientation
import Polyfold.Chapter6.ChartTransfer

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.5,
pp. 227–229: the orientation sets `Or_x^f` of **Theorem 6.37**, orientable neighbourhoods
(**Definition 6.36**), and **Definitions 6.39** and **6.40** *(book 2017: Theorem 6.2,
Definitions 6.10, 6.12 and 6.13; see `BookConcordance.md`)*.

# Orientations of sc-Fredholm sections

## The text, paraphrased

(Definition 6.36) An open neighbourhood `U(x)` of a smooth point on which the local propagation
construction can be carried out is an orientable neighbourhood of `(f, x)`.  (Definition 6.39)
`f` is orientable if there is a map `y ↦ o_y`, an orientation of `DET(f, y)` for every smooth `y`,
such that every smooth point `x` has an orientable neighbourhood `U(x)` on which `y ↦ o_y` is one
of the two continuous orientations.  (Definition 6.40) An orientation of `f` is a map `y ↦ o_y`
such that for every smooth point `x` and every orientable neighbourhood `U(x)` the restriction to
`U(x)_∞` is one of the two continuous orientations.

## What is formalized

* `orChart f x`, `isChart_orChart`, `mem_orChart`: a chosen chart of the atlas at `x`; `Orx f hf x
  hs`, the orientations of `DET(f, x)` read in it; `toChartOr` (`ChartPoint.orTransfer`): the
  identification with the orientations read in any other chart at `x`; `toChartOr_orChart`.
* `IsOrientableNbhd f hf c hc U V x`: `U` open with the local propagation property in the chart
  `c` (`HasLocalPropagation`), `V ⊆ U` open with `x ∈ V`, any two smooth points of `V` joined by
  an sc-smooth path in `U`; `exists_isOrientableNbhd`.
* `restrictOr o hN`: a map `y ↦ o_y` read in the chart `c` over `V`.
* **Definition 6.39**: `IsOrientableSection'`.  **Definition 6.40**: `IsSectionOrientation`.

## Reading

`Or_x^f` is made in a chart point (`LinOrientation.lean`); the text's chart-free `Or_x^f` is read
as the orientations in a chosen chart `orChart f x`, compared with those in other charts by
`orTransfer` (`ChartTransfer.lean`).  As in `ContinuousOrientation.lean`, an orientable
neighbourhood is a pair `V ⊆ U`: the propagation is along paths in `U`, the continuous
orientations live over `V` (Proposition 6.28 gives (1′), not the contractibility of `U`).  "One
of the two continuous orientations" is read as `IsContinuousOrientation`; over an orientable
neighbourhood there are exactly two (`exists_two_isContinuousOrientation`).
-/

open Set

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-! ### The chart-free orientation sets -/

variable (B) in
/-- **A chosen chart at `x`**: a chart of the atlas of the strong bundle whose domain contains `x`
(`StrongBundle.exists_chart_mem`). -/
def orChart (x : X) : StrongBundleChart PX P := (B.exists_chart_mem x).choose

theorem isChart_orChart (x : X) : B.IsChart (orChart B x) :=
  B.isChart_of_mem (B.exists_chart_mem x).choose_spec.1

theorem mem_orChart (x : X) : x ∈ (orChart B x).φ.source :=
  (B.exists_chart_mem x).choose_spec.2

variable (f) in
/-- **`Or_x^f`** (Definition 6.27, Theorem 6.37): the orientations of `DET(f, x)` at a smooth point,
read in the chosen chart `orChart B x`. -/
abbrev Orx (hf : B.IsScFredholmSection f) (x : X) (hs : x ∈ PX.smoothSet) : Type _ :=
  (chartPtOf (orChart B x) (isChart_orChart x) (mem_orChart x) hs).Or f hf

/-- **`Or_x^f` read in another chart**: the identification `ChartPoint.orTransfer` of the
orientations in the chosen chart with those in a chart `c` at `x`. -/
def toChartOr (hf : B.IsScFredholmSection f) {x : X} (hs : x ∈ PX.smoothSet)
    (c : StrongBundleChart PX P) (hc : B.IsChart c) (hx : x ∈ c.φ.source) :
    Orx f hf x hs ≃ (chartPtOf c hc hx hs).Or f hf :=
  (chartPtOf (orChart B x) (isChart_orChart x) (mem_orChart x) hs).orTransfer
    (chartPtOf c hc hx hs) hf hs

/-- In the chosen chart itself the identification is the identity. -/
theorem toChartOr_orChart (hf : B.IsScFredholmSection f) {x : X} (hs : x ∈ PX.smoothSet) :
    toChartOr hf hs (orChart B x) (isChart_orChart x) (mem_orChart x) = Equiv.refl _ :=
  ChartPoint.orTransfer_self _ hf hs

/-! ### Orientable neighbourhoods -/

section Push

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

variable (f) in
/-- **An orientable neighbourhood of `(f, x)`** (Definition 6.36): `U` open with the local
propagation property in the chart `c`, and `V ⊆ U` open with `x ∈ V`, any two smooth points of
`V` being joined by an sc-smooth path in `U`. -/
structure IsOrientableNbhd (hf : B.IsScFredholmSection f) (c : StrongBundleChart PX P)
    (hc : B.IsChart c) (U V : Set X) (x : X) : Prop where
  hasLocalPropagation : HasLocalPropagation f hf c hc U
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  subset : V ⊆ U
  mem : x ∈ V
  path : ∀ y₁ ∈ V, ∀ y₂ ∈ V, y₁ ∈ PX.smoothSet → y₂ ∈ PX.smoothSet →
    ∃ γ : (Fin 1 → ℝ) → X, (rnPolyfold 1).IsScSmoothMap PX γ ∧ γ (pt1 0) = y₁ ∧
      γ (pt1 1) = y₂ ∧ ∀ t, γ t ∈ U

/-- **Orientable neighbourhoods exist** (Theorem 6.35, `exists_nhds_scPath`). -/
theorem exists_isOrientableNbhd
    [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
    [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]
    (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions) (hf : B.IsScFredholmSectionTame f) {x : X} (hx : x ∈ PX.smoothSet) :
    ∃ (c : StrongBundleChart PX P) (hc : B.IsChart c) (U V : Set X),
      IsOrientableNbhd f hf.toIsScFredholmSection c hc U V x := by
  obtain ⟨c, hc, U, hUo, hxU, hU⟩ := theorem_6_35 hX hbump hf hx
  obtain ⟨V, hVo, hxV, hVU, hpath⟩ := exists_nhds_scPath hc hUo hU.subset hxU
  exact ⟨c, hc, U, V, ⟨hU, hUo, hVo, hVU, hxV, hpath⟩⟩

/-- **A map `y ↦ o_y` read in the chart of an orientable neighbourhood** over `V`. -/
def restrictOr {hf : B.IsScFredholmSection f} {c : StrongBundleChart PX P} {hc : B.IsChart c}
    {U V : Set X} {x : X} (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy)
    (hN : IsOrientableNbhd f hf c hc U V x) :
    ∀ y (hy : y ∈ V) (hys : y ∈ PX.smoothSet),
      (chartPtOf c hc (hN.hasLocalPropagation.subset (hN.subset hy)) hys).Or f hf :=
  fun y hy hys => toChartOr hf hys c hc (hN.hasLocalPropagation.subset (hN.subset hy)) (o y hys)

variable (f) in
/-- **Definition 6.39, orientability**: there is a map `y ↦ o_y ∈ Or_y^f` on the smooth points
such that every smooth point `x` has an orientable neighbourhood over which `y ↦ o_y` is a
continuous orientation. -/
def IsOrientableSection' (hf : B.IsScFredholmSection f) : Prop :=
  ∃ o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy, ∀ x ∈ PX.smoothSet,
    ∃ (c : StrongBundleChart PX P) (hc : B.IsChart c) (U V : Set X)
      (hN : IsOrientableNbhd f hf c hc U V x),
      IsContinuousOrientation f hf c hc hN.hasLocalPropagation.subset hN.subset (restrictOr o hN)

variable (f) in
/-- **Definition 6.40, an orientation of `f`**: a map `y ↦ o_y ∈ Or_y^f` on the smooth points
which is a continuous orientation over every orientable neighbourhood of every smooth point. -/
def IsSectionOrientation (hf : B.IsScFredholmSection f)
    (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy) : Prop :=
  ∀ x ∈ PX.smoothSet, ∀ (c : StrongBundleChart PX P) (hc : B.IsChart c) (U V : Set X)
    (hN : IsOrientableNbhd f hf c hc U V x),
    IsContinuousOrientation f hf c hc hN.hasLocalPropagation.subset hN.subset (restrictOr o hN)

end Push

end Polyfold
