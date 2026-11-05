import Polyfold
/-! Blind formalization of V2_57 (the text's §2.5, Definition 2.50, pp. 51–52).

Text: for `P : Y → X` (`Y` paracompact Hausdorff, fibres Banachable), a strong bundle chart
`(Φ, P⁻¹(V), K, U ◁ F)`: `K = R(U ◁ F)`, `V` open with a homeomorphism `φ : V → O`,
`Φ : P⁻¹(V) → K` a homeomorphism covering `φ`, bounded linear on fibres.  Charts are compatible
if `(Φ' ∘ Φ⁻¹)[i]` are sc-diffeomorphisms, `i = 0, 1`; atlases and their equivalence.

Choices:
- This item is a definition.  Setting: `X Y : Type` (universe 0).  `Y` is Hausdorff and
  paracompact, `P : Y → X`, each fibre `P⁻¹(x)` carries a real vector space structure (instance
  arguments, as the project does) and is Banachable (the project's `IsBanachable`, checked with
  `#print`: linearly homeomorphic, in the subspace topology, to a Banach space).  I also assume
  `P` continuous: the text needs `P⁻¹(V)` open for the chart domains to be open and the overlaps
  `Φ(P⁻¹(V ∩ V'))` to be open in `K` (hence retracts); Definition 2.51 has `P` continuous.
- `X`: the item does not say what `X` is beyond a space.  To compare with the project, `X` is a
  Hausdorff paracompact space with an M-polyfold structure `PX : MPolyfold X`.  My chart notion
  (`IsStrongBundleChartB`) only uses the topology of `X`.
- Chart data (`ChartDataB`): `φ : MChart X` — exactly "an open `V` with a homeomorphism
  `φ : V → O`" onto an sc-smooth retract `(O, C, E)` (the project's `MChart`, Definition 2.11,
  checked with `#print`: a local model and a `PartialEquiv` with open source `V`, target `O`,
  continuous both ways; no compatibility with an atlas is built in); the fibre model `F`; `U ⊆ E₀`;
  `R : E₀ × F₀ → E₀ × F₀`; `Φ : PartialEquiv Y (E₀ × F₀)`.
- Strong bundle chart (`IsStrongBundleChartB`): `U` relatively open in `C`; `R` a strong bundle
  retraction on `U ◁ F` (my `IsStrongBundleRetractionB`, copied from
  `RoundTrip/Blind/V2_54.lean`); `K = R(U ◁ F)` covers `O`: `r(U) = O` (`baseB`); `Φ` has source
  `P⁻¹(V)` and target `K` and is a homeomorphism between them; `Φ` covers `φ`:
  `p(Φ(y)) = φ(P(y))`; on each fibre `P⁻¹(x)`, `x ∈ V`, the fibre part `v ↦ (Φ v).2 ∈ F₀` is
  linear and continuous (bounded).
- The project's `StrongBundleChart PX P` additionally requires `φ` to be a chart of the
  M-polyfold `PX` (`PX.IsChart φ`).  The item only says "a homeomorphism `φ : V → O`".  B therefore
  compares the project's charts with MY charts whose `φ` is a chart of `PX`: every project chart
  is a text chart, and every text chart with `PX.IsChart φ` is a project chart.  THIS EXTRA
  CONDITION IS A POSSIBLE DISCREPANCY (it is harmless if the text means `φ` to be a chart of the
  M-polyfold `X`, or if `X` gets its M-polyfold structure from the bundle atlas).
- Compatibility (`CompatibleB`): with `A = Φ(P⁻¹(V ∩ V'))`, `A' = Φ'(P⁻¹(V ∩ V'))`
  (`overlapB`), `Φ' ∘ Φ⁻¹ : A → A'` (`transitionB`) and its inverse `Φ ∘ Φ'⁻¹`: (i = 0) the two
  maps are mutually inverse sc-smooth maps between the retracts `(A, C ◁ F, E ⊕ F)` and
  `(A', C' ◁ F', E' ⊕ F')` (`IsScDiffeoRetractB`, from my `IsScSmoothRetractMapB` = Definition 2.7
  as in `RoundTrip/Blind/V2_6.lean`); (i = 1) the induced maps `(Φ' ∘ Φ⁻¹)[1] : A[1] → A'[1]`
  and back, `A[1] = A ∩ (E₀ ⊕ F₁) ⊆ (E ⊕ F¹)₀` (`oneB`), exist (lifts of the fibre components to
  `F'₁`, resp. `F₁`) and are mutually inverse sc-smooth maps between `(A[1], C ◁ F¹, E ⊕ F¹)` and
  `(A'[1], C' ◁ F'¹, E' ⊕ F'¹)`.  B asserts that the project's `StrongBundleChart.Compatible` is
  this (for project charts).
- Atlas (`IsAtlasB`): a set of charts, pairwise compatible, whose domains `P⁻¹(V)` cover `Y`.
  Equivalence (`AtlasEquivB`): the union is an atlas.  B asserts that the project's
  `StrongBundleAtlas` (its chart sets) and `StrongBundleAtlas.Equiv` are these.  I do not add the
  presupposition that atlas equivalence is an equivalence relation (that belongs to the
  equivalence classes of Definition 2.51).
- Nothing looks false to me.
-/
namespace RoundTrip.V2_57
open Polyfold

/-- `(U ◁ F)_{m,k} = U_m ⊕ F_k` (as in `V2_54`). -/
def doubleLevelB (E F : ScBanach) (U : Set (E.lvl 0)) (m k : ℕ) : Set (E.lvl m × F.lvl k) :=
  {q | E.toBase m q.1 ∈ U}

/-- Definition 2.47: a strong bundle map (as in `V2_54`). -/
def IsStrongBundleMapB {E F E' F' : ScBanach} (U : Set (E.lvl 0)) (U' : Set (E'.lvl 0))
    (Φ : E.lvl 0 × F.lvl 0 → E'.lvl 0 × F'.lvl 0) : Prop :=
  (∃ φ : E.lvl 0 → E'.lvl 0, ∀ u ∈ U, φ u ∈ U' ∧ ∀ h : F.lvl 0, (Φ (u, h)).1 = φ u) ∧
  (∀ u ∈ U, IsLinearMap ℝ (fun h : F.lvl 0 => (Φ (u, h)).2)) ∧
  (∀ m k : ℕ, k ≤ m + 1 → ∀ q ∈ doubleLevelB E F U m k,
    ∃ q' : E'.lvl m × F'.lvl k,
      Φ (E.toBase m q.1, F.toBase k q.2) = (E'.toBase m q'.1, F'.toBase k q'.2)) ∧
  IsScSmooth (E := E.prod F) (F := E'.prod F') (U ×ˢ Set.univ) Φ ∧
  (∃ Φ₁ : (E.prod F.shift).lvl 0 → (E'.prod F'.shift).lvl 0,
    (∀ u ∈ U, ∀ h : F.lvl 1,
      (Φ₁ (u, h)).1 = (Φ (u, F.toBase 1 h)).1 ∧
      F'.toBase 1 (Φ₁ (u, h)).2 = (Φ (u, F.toBase 1 h)).2) ∧
    IsScSmooth (E := E.prod F.shift) (F := E'.prod F'.shift) (U ×ˢ Set.univ) Φ₁)

/-- Definition 2.47: a strong bundle retraction (as in `V2_54`). -/
def IsStrongBundleRetractionB {E F : ScBanach} (U : Set (E.lvl 0))
    (R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0) : Prop :=
  IsStrongBundleMapB U U R ∧ ∀ u ∈ U, ∀ h : F.lvl 0, R (R (u, h)) = R (u, h)

/-- `O = r(U)`, `r(u)` the first component of `R(u, 0)`. -/
def baseB {E F : ScBanach} (U : Set (E.lvl 0)) (R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0) :
    Set (E.lvl 0) :=
  (fun u => (R (u, 0)).1) '' U

/-- Definition 2.7: `f : O → O'` is sc-smooth between retracts (as in `V2_6`). -/
def IsScSmoothRetractMapB (E : ScBanach) (C O : Set (E.lvl 0)) (E' : ScBanach)
    (O' : Set (E'.lvl 0)) (f : E.lvl 0 → E'.lvl 0) : Prop :=
  Set.MapsTo f O O' ∧ ∃ ρ : ScRetraction E C, ρ.retract = O ∧ IsScSmooth ρ.U (f ∘ ρ.toFun)

/-- `g : A → A'` is an sc-diffeomorphism between the retracts `(A, C, E)` and `(A', C', E')`,
with inverse `g'`. -/
def IsScDiffeoRetractB (E : ScBanach) (C A : Set (E.lvl 0)) (E' : ScBanach)
    (C' A' : Set (E'.lvl 0)) (g : E.lvl 0 → E'.lvl 0) (g' : E'.lvl 0 → E.lvl 0) : Prop :=
  IsScSmoothRetractMapB E C A E' A' g ∧ IsScSmoothRetractMapB E' C' A' E A g' ∧
    (∀ a ∈ A, g' (g a) = a) ∧ (∀ a' ∈ A', g (g' a') = a')

/-- `A[1] = A ∩ (E₀ ⊕ F₁)`, as a subset of `(E ⊕ F¹)₀ = E₀ × F₁`. -/
def oneB {E F : ScBanach} (A : Set (E.lvl 0 × F.lvl 0)) : Set ((E.prod F.shift).lvl 0) :=
  {q | (q.1, F.toBase 1 q.2) ∈ A}

/-- `g₁` is the map `A[1] → (E' ⊕ F'¹)₀` induced by `g` (fibre component lifted to `F'₁`). -/
def IsLiftOnB {E F E' F' : ScBanach} (A : Set (E.lvl 0 × F.lvl 0))
    (g : E.lvl 0 × F.lvl 0 → E'.lvl 0 × F'.lvl 0)
    (g₁ : (E.prod F.shift).lvl 0 → (E'.prod F'.shift).lvl 0) : Prop :=
  ∀ q ∈ oneB A, (g₁ q).1 = (g (q.1, F.toBase 1 q.2)).1 ∧
    F'.toBase 1 (g₁ q).2 = (g (q.1, F.toBase 1 q.2)).2

/-- The data `(Φ, P⁻¹(V), K, U ◁ F)` of a candidate strong bundle chart: the homeomorphism
`φ : V → O` (with its local model `(O, C, E)`), the fibre model `F`, `U`, the retraction `R`, and
`Φ`. -/
structure ChartDataB (X Y : Type) [TopologicalSpace X] where
  φ : MChart X
  F : ScBanach
  U : Set (φ.model.E.lvl 0)
  R : φ.model.E.lvl 0 × F.lvl 0 → φ.model.E.lvl 0 × F.lvl 0
  Φ : PartialEquiv Y (φ.model.E.lvl 0 × F.lvl 0)

section
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Definition 2.50**: a strong bundle chart `(Φ, P⁻¹(V), K, U ◁ F)` for `P : Y → X`. -/
def IsStrongBundleChartB (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})]
    [∀ x, Module ℝ (P ⁻¹' {x})] (d : ChartDataB X Y) : Prop :=
  -- `U` relatively open in `C`, `R` a strong bundle retraction on `U ◁ F`
  IsRelOpenInQuadrant d.φ.model.E d.φ.model.C d.U ∧
  IsStrongBundleRetractionB d.U d.R ∧
  -- `K = R(U ◁ F)` covers the retract `O = r(U)`
  baseB d.U d.R = d.φ.model.O ∧
  -- `Φ : P⁻¹(V) → K` is a homeomorphism
  d.Φ.source = P ⁻¹' d.φ.source ∧
  d.Φ.target = d.R '' (d.U ×ˢ Set.univ) ∧
  ContinuousOn d.Φ d.Φ.source ∧ ContinuousOn d.Φ.symm d.Φ.target ∧
  -- `Φ` covers `φ`
  (∀ y ∈ d.Φ.source, (d.Φ y).1 = d.φ.toPartialEquiv (P y)) ∧
  -- `Φ` is bounded linear on the fibres
  (∀ x ∈ d.φ.source,
    IsLinearMap ℝ (fun v : P ⁻¹' {x} => (d.Φ v).2) ∧ Continuous (fun v : P ⁻¹' {x} => (d.Φ v).2))

/-- The overlap `Φ(P⁻¹(V ∩ V'))`, in the chart `d`. -/
def overlapB (d d' : ChartDataB X Y) : Set (d.φ.model.E.lvl 0 × d.F.lvl 0) :=
  d.Φ '' (d.Φ.source ∩ d'.Φ.source)

/-- The transition `Φ' ∘ Φ⁻¹`. -/
def transitionB (d d' : ChartDataB X Y) :
    d.φ.model.E.lvl 0 × d.F.lvl 0 → d'.φ.model.E.lvl 0 × d'.F.lvl 0 :=
  d'.Φ ∘ d.Φ.symm

/-- **Definition 2.50**: compatibility: `(Φ' ∘ Φ⁻¹)[i]` are sc-diffeomorphisms, `i = 0, 1`. -/
def CompatibleB (d d' : ChartDataB X Y) : Prop :=
  IsScDiffeoRetractB (d.φ.model.E.prod d.F) (d.φ.model.C ×ˢ Set.univ) (overlapB d d')
    (d'.φ.model.E.prod d'.F) (d'.φ.model.C ×ˢ Set.univ) (overlapB d' d)
    (transitionB d d') (transitionB d' d) ∧
  ∃ (g₁ : (d.φ.model.E.prod d.F.shift).lvl 0 → (d'.φ.model.E.prod d'.F.shift).lvl 0)
    (g₁' : (d'.φ.model.E.prod d'.F.shift).lvl 0 → (d.φ.model.E.prod d.F.shift).lvl 0),
    IsLiftOnB (overlapB d d') (transitionB d d') g₁ ∧
    IsLiftOnB (overlapB d' d) (transitionB d' d) g₁' ∧
    IsScDiffeoRetractB (d.φ.model.E.prod d.F.shift) (d.φ.model.C ×ˢ Set.univ)
      (oneB (overlapB d d')) (d'.φ.model.E.prod d'.F.shift) (d'.φ.model.C ×ˢ Set.univ)
      (oneB (overlapB d' d)) g₁ g₁'

/-- **Definition 2.50**: a strong bundle atlas: pairwise compatible charts covering `Y`. -/
def IsAtlasB (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (𝒜 : Set (ChartDataB X Y)) : Prop :=
  (∀ d ∈ 𝒜, IsStrongBundleChartB P d) ∧ (∀ d ∈ 𝒜, ∀ d' ∈ 𝒜, CompatibleB d d') ∧
    ∀ y : Y, ∃ d ∈ 𝒜, y ∈ d.Φ.source

/-- **Definition 2.50**: two atlases are equivalent if their union is an atlas. -/
def AtlasEquivB (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (𝒜 𝒜' : Set (ChartDataB X Y)) : Prop :=
  IsAtlasB P (𝒜 ∪ 𝒜')

end

/-- The data of a project strong bundle chart. -/
def toDataB {X Y : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
    [TopologicalSpace Y] {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (c : StrongBundleChart PX P) : ChartDataB X Y :=
  ⟨c.φ, c.F, c.U, c.R, c.toPartialEquiv⟩

/-- Definition 2.50: strong bundle charts, their compatibility, atlases and their equivalence;
the project's notions are these (charts: those whose `φ` is a chart of `X`). -/
def B : Prop :=
  ∀ (X Y : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})],
    Continuous P → (∀ x, IsBanachable (P ⁻¹' {x})) →
      -- strong bundle charts
      (∀ c : StrongBundleChart PX P, IsStrongBundleChartB P (toDataB c)) ∧
      (∀ d : ChartDataB X Y, PX.IsChart d.φ → IsStrongBundleChartB P d →
        ∃ c : StrongBundleChart PX P, toDataB c = d) ∧
      -- compatibility
      (∀ c c' : StrongBundleChart PX P, c.Compatible c' ↔ CompatibleB (toDataB c) (toDataB c')) ∧
      -- atlases
      (∀ A : StrongBundleAtlas PX P, IsAtlasB P (toDataB '' A.charts)) ∧
      (∀ 𝒜 : Set (ChartDataB X Y), (∀ d ∈ 𝒜, PX.IsChart d.φ) → IsAtlasB P 𝒜 →
        ∃ A : StrongBundleAtlas PX P, toDataB '' A.charts = 𝒜) ∧
      -- equivalence of atlases
      (∀ A A' : StrongBundleAtlas PX P,
        A.Equiv A' ↔ AtlasEquivB P (toDataB '' A.charts) (toDataB '' A'.charts))

end RoundTrip.V2_57
