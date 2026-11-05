import Polyfold
/-! Blind formalization of V3_14 (the text's §3.1, Theorem 3.12, p. 70). Choices:
- Setting: `X Y : Type` (universe 0, as asked).  `PX : MPolyfold X`, `P : Y → X` with the
  fibrewise linear structure as instances on `P ⁻¹' {x}`, `Bd : StrongBundle PX P`.
- "tame strong bundle": defined here (`IsTameStrongBundle`) as: the base `X` is tame
  (`MPolyfold.IsTame`, Definition 2.37) and the bundle structure has an *equivalent* strong bundle
  atlas all of whose charts have a tame base retraction `r` (a tame strong bundle retraction is one
  whose `r` is tame, Definition 2.34; `ScRetraction.IsTame`).  This is a property of the given
  structure (an existential over atlases), not the unsatisfiable "every compatible chart is tame".
- "`f` an sc-smooth section": `StrongBundle.IsScSmoothSection` (Definition 2.52).
- "`(f, x₀)` an sc-Fredholm germ": since the bundle is tame, I read Definition 3.11 with its germ
  data in a *tame* strong bundle chart: `StrongBundle.IsScFredholmGermTame` (the text's recall,
  Definition 3.50, of Definition 3.11 for tame strong bundles).  It includes that `x₀` is smooth.
  (The variant `IsScFredholmGerm`, data in any compatible chart, would be a weaker hypothesis.)
- `f(x₀) = 0`: `IsZeroAt P f x₀` (the value is the zero of the fibre).
- `X₀` is `X` with its own topology; "open neighbourhoods of `x₀` in `X₀`" are open sets of `X`
  containing `x₀`; "nested" = `O (i+1) ⊆ O i`.
- "`cl_{X₀}{x ∈ O(i) | f(x) = 0}` is a compact subset of `X_i`": the closure `K` (taken in `X`)
  lies in the level set `X_i = PX.levelSet i`, and `K`, seen in `X_i`, is compact for the level
  topology `PX.levelTopology i` (the topology of `X_i` of the paragraph after Definition 2.14, not
  the subspace topology from `X`).
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_14
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- A **tame strong bundle**: tame base, and an equivalent strong bundle atlas of charts whose base
retractions are tame. -/
def IsTameStrongBundle (Bd : StrongBundle PX P) : Prop :=
  PX.IsTame ∧ ∃ A : StrongBundleAtlas PX P, A.Equiv Bd.atlas ∧
    ∀ c ∈ A.charts, (IsStrongBundleRetraction.baseRetraction c.relOpen c.isRetraction).IsTame

end

/-- Theorem 3.12: at a zero `x₀` of an sc-Fredholm germ there are nested open neighbourhoods
`O(i)` of `x₀` such that the closure in `X₀` of the zeros in `O(i)` is a compact subset of `X_i`. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x₀ : X),
    IsTameStrongBundle Bd → Bd.IsScSmoothSection f → Bd.IsScFredholmGermTame f x₀ →
    IsZeroAt P f x₀ →
      ∃ O : ℕ → Set X,
        (∀ i, IsOpen (O i) ∧ x₀ ∈ O i ∧ O (i + 1) ⊆ O i) ∧
        ∀ i, closure {x | x ∈ O i ∧ IsZeroAt P f x} ⊆ PX.levelSet i ∧
          @IsCompact (PX.levelSet i) (PX.levelTopology i)
            {p | (p : X) ∈ closure {x | x ∈ O i ∧ IsZeroAt P f x}}

end RoundTrip.V3_14
