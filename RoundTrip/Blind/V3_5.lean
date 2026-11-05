import Polyfold
/-! Blind formalization of V3_5 (the text's §3.1, Definition 3.3, p. 63). Choices:
- This item is a definition; the text asserts no further property.  Setting (as in the blind
  V3_14/V3_17): `X Y : Type` (universe 0; nothing depends on it), `PX : MPolyfold X`,
  `P : Y → X` with the fibre linear structures as instances, `Bd : StrongBundle PX P`.
- "a strong bundle chart" (`Φ : P⁻¹(V') → K` covering `φ : V' → O`, `K = R(U ◁ F)`,
  `O = r(U)`): the project's `StrongBundleChart PX P` compatible with the bundle's atlas
  (`Bd.IsChart c`, i.e. a chart of the maximal atlas).  I read the fields with `#print`:
  `c.φ` the base chart with model `(E, C, O)`, `c.U ⊆ E₀`, `c.R`, `c.toPartialEquiv` (= `Φ`).
  "In a strong bundle chart" is read existentially (one chart with `φ(x₀) = 0`).
- `r(u) = (R(u, 0))₁` (`baseB`), and the principal part `𝐟(z) = (Φ(f(φ⁻¹ z)))₂` (`principalB`;
  `Φ ∘ f ∘ φ⁻¹ (z) = (z, 𝐟(z))` since `Φ` covers `φ` and `f` is a section).
- "a continuous section `f : V → P⁻¹(V)` near the smooth point `x₀`": `x₀ ∈ X_∞`
  (`PX.smoothSet`), and an open `V ∋ x₀` with `P(f(x)) = x` and `f` continuous on `V` (`f` is a
  total map `X → Y`; values off `V` are irrelevant).
- "`𝐟 ∘ r : O(C, 0) → F` an sc-smooth germ": there is an sc-germ of neighbourhoods
  `G = O(C, 0)` (the project's `ScNbhdGerm`, Definition 3.1, audited in V3_1) with `G₀ ⊆ U` and
  `φ⁻¹(r(G₀)) ⊆ V` (so `𝐟 ∘ r` is computed from the section `f` on `G₀`), on which `𝐟 ∘ r` is
  sc-smooth (the project's `IsScSmoothGerm`, Definition 3.2, audited in V3_2).  The germ `G` is
  existential: "the size of the sets `U_m` does not matter" (Definition 3.1), so I do not require
  the levels to be `U ∩ E_m` for the chart's `U`.
- B: for a section `f` (`P ∘ f = id` on all of `X`, as the project's notion requires), the
  project's `StrongBundle.IsScSmoothSectionGerm` is equivalent to mine.
- Nothing looks false to me.
-/
namespace RoundTrip.V3_5
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- The base retraction `r(u) = (R(u, 0))₁` of the chart's strong bundle retraction. -/
def baseB (c : StrongBundleChart PX P) (u : c.φ.model.E.lvl 0) : c.φ.model.E.lvl 0 :=
  (c.R (u, 0)).1

/-- The principal part `𝐟` of `Φ ∘ f ∘ φ⁻¹ (z) = (z, 𝐟(z))`. -/
def principalB (c : StrongBundleChart PX P) (f : X → Y) (z : c.φ.model.E.lvl 0) : c.F.lvl 0 :=
  (c.toPartialEquiv (f (c.φ.toPartialEquiv.symm z))).2

/-- **Definition 3.3**: `(f, x₀)` is an sc-smooth section germ of `P : Y → X`. -/
def IsScSmoothSectionGermB (Bd : StrongBundle PX P) (f : X → Y) (x₀ : X) : Prop :=
  x₀ ∈ PX.smoothSet ∧
  ∃ V : Set X, IsOpen V ∧ x₀ ∈ V ∧ (∀ x ∈ V, P (f x) = x) ∧ ContinuousOn f V ∧
    ∃ c : StrongBundleChart PX P, Bd.IsChart c ∧ x₀ ∈ c.φ.source ∧
      c.φ.toPartialEquiv x₀ = 0 ∧
      ∃ G : ScNbhdGerm c.φ.model.E c.φ.model.C,
        (∀ u ∈ G.U 0, u ∈ c.U ∧ c.φ.toPartialEquiv.symm (baseB c u) ∈ V) ∧
        IsScSmoothGerm G (principalB c f ∘ baseB c)

end

/-- Definition 3.3: for a section `f`, the project's sc-smooth section germs are the text's. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x₀ : X),
    (∀ x, P (f x) = x) →
      (Bd.IsScSmoothSectionGerm f x₀ ↔ IsScSmoothSectionGermB Bd f x₀)

end RoundTrip.V3_5
