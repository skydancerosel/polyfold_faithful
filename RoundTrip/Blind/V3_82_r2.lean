import Polyfold
/-! Blind formalization of V3_82 (the text's §3.6, Theorem 3.54 (1), p. 111; proof p. 114),
second blind statement (r2).  Choices:
- Setting (Theorem 3.54): `X Y : Type` (universe 0, as instructed; nothing depends on the
  universe).  `PX : MPolyfold X`, `P : Y → X` with the fibrewise linear structure as instances on
  `P ⁻¹' {x}`, `Bd : StrongBundle PX P` (Definition 2.51).  The quote ("at every zero `y` near `x`")
  presupposes the hypotheses of Theorem 3.54, which I added exactly: `Bd` tame, `f` an sc-Fredholm
  section, `f(x) = 0`, `(f, x)` in good position.
- "tame strong bundle": `IsTameStrongBundle`, defined here (no project notion in the vocabulary):
  tame base (`MPolyfold.IsTame`, Definition 2.37) and an *equivalent* strong bundle atlas all of
  whose charts have a tame base retraction (`ScRetraction.IsTame`, Definition 2.34).  A property of
  the given structure (existence of a tame atlas), not "every chart is tame".
- "sc-Fredholm section" (§3.6, tame strong bundle): `StrongBundle.IsScFredholmSectionTame`
  (Definition 3.51, germ reading: sc-smooth, regularizing, sc-Fredholm germ data at every smooth
  point in a tame chart).  Doubt: if the text means Definition 3.14 without asking the germ data to
  be in a tame chart, this hypothesis is slightly stronger than the text.
- `f(x) = 0`: `IsZeroAt P f x`.
- "`(f, y)` is in good position" (Definition 3.53: `f'(y)` onto, kernel in good position to the
  partial cone), both in the hypothesis at `x` and in the conclusion at `y`:
  `StrongBundle.IsGoodPositionGermSc` (germ reading of Definition 3.11 in a tame strong bundle chart
  centred at the point, `Tf̃(0)` onto `K₀`, `ker` in good position to `C₀O` inside `T₀O` with the
  text's *sc-complement*, Definition 3.21 as written).  I did not use the whole-chart variants
  (stricter than the text) nor `IsGoodPositionGermTame` (algebraic complement only).  The project
  states the kernel condition without the text's case distinction `d_X(·) ≥ 1`; at a point with
  `d_X = 0` that condition holds automatically (Corollary 3.24), so I accepted it.
- "at every zero `y` near `x`": there is an open `V ∋ x` such that the claim holds at every
  `y ∈ V` with `f(y) = 0` (`zeroSetIn`).
- The item's title mentions "the filler condition at the nearby zeros"; that is not a hypothesis of
  the text's Theorem 3.54 (which assumes only that `(f, x)` is in good position), so I did not add
  it (`IsGoodPositionGermFilled` is not used).  "(from Corollary 3.41 and Lemma 3.55)" names the
  proof and is not formalized.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_82_r2
open Polyfold

/-- `S(f, V) = {y ∈ V | f(y) = 0}`. -/
def zeroSetIn {X Y : Type} (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] (f : X → Y)
    (V : Set X) : Set X :=
  {y | y ∈ V ∧ IsZeroAt P f y}

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

/-- Theorem 3.54 (1): if `(f, x)` is in good position at a zero `x` of an sc-Fredholm section of a
tame strong bundle, then there is an open `V ∋ x` such that `(f, y)` is in good position at every
zero `y ∈ V`. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x : X),
    IsTameStrongBundle Bd → Bd.IsScFredholmSectionTame f → IsZeroAt P f x →
    Bd.IsGoodPositionGermSc f x →
      ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
        ∀ y ∈ zeroSetIn P f V, Bd.IsGoodPositionGermSc f y

end RoundTrip.V3_82_r2
