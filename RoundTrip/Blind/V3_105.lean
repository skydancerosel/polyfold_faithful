import Polyfold
/-! Blind formalization of V3_105 (the text's §3.1, Theorem 3.15, p. 71, as recalled for tame
germ data after Definition 3.51, p. 110). Choices:
- Setting: `X Y : Type` (universe 0; nothing depends on the universe).  `PX : MPolyfold X`,
  `P : Y → X` with the fibrewise linear structure as instances on `P ⁻¹' {x}`, and
  `Bd : StrongBundle PX P` (Definition 2.51).
- "the tame strong bundle": `IsTameStrongBundle` (defined here, as in the earlier blind files):
  tame base (`MPolyfold.IsTame`, Definition 2.37) and an *equivalent* strong bundle atlas all of
  whose charts have a tame base retraction (`ScRetraction.IsTame`, Definition 2.34).  This is a
  property of the given structure (an existential over atlases), not "every compatible chart is
  tame" (which would be unsatisfiable in general).
- "sc-Fredholm section" with tame germ data (the item's title, and the §3.6 recall):
  `StrongBundle.IsScFredholmSectionTame` (Definition 3.51: Definition 3.14 with the germ data of
  Definition 3.11 at every smooth point in a tame strong bundle chart, Definition 3.50), used both
  in the hypothesis and in the conclusion.
- "`s` an sc⁺-section": `StrongBundle.IsScPlusSection` (Definition 2.52).
- `f + s`: the fibrewise sum `sectionAdd P f s` (its junk branch is never reached, both being
  sections).
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_105
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

/-- Theorem 3.15 (tame germ data): an sc-Fredholm section of a tame strong bundle perturbed by an
sc⁺-section is again an sc-Fredholm section. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f s : X → Y),
    IsTameStrongBundle Bd → Bd.IsScFredholmSectionTame f → Bd.IsScPlusSection s →
      Bd.IsScFredholmSectionTame (sectionAdd P f s)

end RoundTrip.V3_105
