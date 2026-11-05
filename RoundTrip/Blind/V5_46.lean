import Polyfold
/-! Blind formalization of V5_46 (the text's §5.3, Lemma 5.26, p. 187; also p. 179: "clearly
general position implies good position").

Text: for an sc-Fredholm section `f` over a tame `X`: if `f` is in general position, then `f` is
in good position.

Choices:
- Setting: `X Y : Type` (universe 0, as asked); `PX : MPolyfold X`, `P : Y → X` with the
  fibrewise linear structure as instances on the fibres, `Bd : StrongBundle PX P`.
- "over a tame `X`": as in `RoundTrip/Blind/V5_40.lean` / `V5_45.lean`, the tame setting of §5.3
  (good position, Definition 3.53, and general position, Definition 5.17, are notions for tame
  strong bundles, computed in tame charts): `IsTameStrongBundle Bd` (`PX.IsTame`, Definition 2.37,
  and an EQUIVALENT strong bundle atlas whose charts have tame base retractions — a property of the
  given structure, not "every chart is tame"), and `f` sc-Fredholm in the tame sense,
  `Bd.IsScFredholmSectionTame f` (Definition 3.51).
- "`f` in general position" / "in good position": both notions are defined for germs `(f, x)` at
  zeros `x` (Definitions 5.17, 3.53); a section is in general (good) position if it is so at every
  zero.  The proof is pointwise ("clearly general position implies good position"), so I state the
  pointwise form, which implies the section form: at every zero `x` of `f`, if `(f, x)` is in
  general position then `(f, x)` is in good position.
- General position: the project's `Bd.IsGeneralPositionGerm f x` (Definition 5.17, compared with
  the text in `RoundTrip/Blind/V5_31.lean`: in a tame strong bundle chart around `x`, the
  linearization is onto and its kernel has an sc-complement inside the reduced tangent space).
- Good position: the project's `Bd.IsGoodPositionGermTame f x` (Definition 3.53 in a tame chart,
  checked with `#print`: `x` smooth, a tame strong bundle chart centred at `x` with sc-Fredholm
  germ data — filled version `g`, sc⁺ part `s`, `g − s` conjugated to a basic germ — such that the
  germ is in good position, `IsGoodPositionAt`: `Dg(0)|_{T₀O}` onto `K₀` and its kernel in good
  position to the partial cone `C₀O` in `T₀O`), as in V5_29, V5_40, V5_45.
- `f(x) = 0`: `IsZeroAt P f x`.
- Nothing looks false to me.
-/
namespace RoundTrip.V5_46
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

/-- Lemma 5.26: for an sc-Fredholm section of a tame strong bundle, at every zero, general
position implies good position. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y),
    IsTameStrongBundle Bd → Bd.IsScFredholmSectionTame f →
      ∀ x : X, IsZeroAt P f x → Bd.IsGeneralPositionGerm f x → Bd.IsGoodPositionGermTame f x

end RoundTrip.V5_46
