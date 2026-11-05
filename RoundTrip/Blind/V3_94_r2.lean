import Polyfold
/-! Blind formalization of V3_94 (the text's §3.6, Theorem 3.54 (1), (2), p. 111), second blind
statement (r2).  `B` is the conjunction of (1) and (2), for one and the same `V`.  Choices:
- Setting (Theorem 3.54): `X Y : Type` (universe 0, as instructed; nothing depends on the
  universe).  `PX : MPolyfold X`, `P : Y → X` with the fibrewise linear structure as instances on
  `P ⁻¹' {x}`, `Bd : StrongBundle PX P` (Definition 2.51).
- "tame strong bundle": `IsTameStrongBundle`, defined here (no project notion in the vocabulary):
  tame base (`MPolyfold.IsTame`, Definition 2.37) and an *equivalent* strong bundle atlas all of
  whose charts have a tame base retraction (`ScRetraction.IsTame`, Definition 2.34).  A property of
  the given structure (existence of a tame atlas), not "every chart is tame".
- "sc-Fredholm section" (§3.6, tame strong bundle): `StrongBundle.IsScFredholmSectionTame`
  (Definition 3.51, germ reading: sc-smooth, regularizing, sc-Fredholm germ data at every smooth
  point in a tame chart).  Doubt: if the text means Definition 3.14 without asking the germ data to
  be in a tame chart, this hypothesis is slightly stronger than the text.
- `f(x) = 0`: `IsZeroAt P f x`.
- "`(f, x)` / `(f, y)` in good position" (Definition 3.53), in the hypothesis and in (1):
  `StrongBundle.IsGoodPositionGermSc` (germ reading of Definition 3.11 in a tame strong bundle chart
  centred at the point, `Tf̃(0)` onto `K₀`, `ker` in good position to `C₀O` inside `T₀O` with the
  text's *sc-complement*, Definition 3.21 as written).  I did not use the whole-chart variants
  (stricter than the text), nor `IsGoodPositionGermTame` (algebraic complement only), nor
  `IsGoodPositionGermFilled` (an extra filler condition at nearby zeros, not in the text).  The
  project states the kernel condition without the text's case distinction `d_X(·) ≥ 1`; at a point
  with `d_X = 0` it holds automatically (Corollary 3.24), so I accepted it.
- `S = {y ∈ V | f(y) = 0}`: `zeroSetIn P f V`, `V` open with `x ∈ V`.
- (2) "`S` is a sub-M-polyfold": `MPolyfold.IsSubMPolyfold` (Definition 2.20).  "its induced
  structure": `MPolyfold.subPolyfold` (Proposition 2.21), which needs `S` paracompact as an instance;
  paracompactness is asserted as part of the claim (it is true: M-polyfolds are metrizable).
  "equivalent to a smooth manifold with boundary with corners": `MPolyfold.HasCornerStructure`
  (Definition 4.1: an equivalent atlas of corner charts onto relatively open subsets of partial
  quadrants in finite-dimensional spaces with the constant sc-structure; the dimension is not fixed
  by the statement, and the definition lets it vary from chart to chart).
- The item's title ("with the text's hypotheses") matches what `B` does.  The quote is identical
  to that of V3_85, and so is `B`.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_94_r2
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

/-- Theorem 3.54 (1), (2): if `(f, x)` is in good position at a zero `x` of an sc-Fredholm section
of a tame strong bundle, there is an open `V ∋ x` such that, with `S = {y ∈ V | f(y) = 0}`,
(1) `(f, y)` is in good position at every `y ∈ S`, and (2) `S` is a sub-M-polyfold whose induced
structure is equivalent to a smooth manifold with boundary with corners. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x : X),
    IsTameStrongBundle Bd → Bd.IsScFredholmSectionTame f → IsZeroAt P f x →
    Bd.IsGoodPositionGermSc f x →
      ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
        -- (1)
        (∀ y ∈ zeroSetIn P f V, Bd.IsGoodPositionGermSc f y) ∧
        -- (2)
        ∃ (hS : PX.IsSubMPolyfold (zeroSetIn P f V)) (_ : ParacompactSpace (zeroSetIn P f V)),
          (PX.subPolyfold hS).HasCornerStructure

end RoundTrip.V3_94_r2
