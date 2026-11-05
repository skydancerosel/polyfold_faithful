import Polyfold
/-! Blind formalization of V3_100 (the text's §3.6, after Theorem 3.54, p. 111, with the remark
citing Corollary 3.24, p. 79), second blind statement (r2).  `B` is the conjunction of the two
quoted claims.  Choices:
- Setting: that of Definition 3.53, which both quotes are about: `X Y : Type` (universe 0, as
  instructed; nothing depends on the universe), `PX : MPolyfold X`, `P : Y → X` with the fibrewise
  linear structure as instances on `P ⁻¹' {x}`, `Bd : StrongBundle PX P` tame, `f` an sc-Fredholm
  section, `x` a zero of `f`.  These hypotheses are presupposed by "`(f, x)` is in good position";
  I added exactly them.
- "tame strong bundle": `IsTameStrongBundle`, defined here (no project notion in the vocabulary):
  tame base (`MPolyfold.IsTame`, Definition 2.37) and an *equivalent* strong bundle atlas all of
  whose charts have a tame base retraction (`ScRetraction.IsTame`, Definition 2.34).  A property of
  the given structure (existence of a tame atlas), not "every chart is tame".
- "sc-Fredholm section" (§3.6): `StrongBundle.IsScFredholmSectionTame` (Definition 3.51, germ
  reading, germ data at every smooth point in a tame chart).  `f(x) = 0`: `IsZeroAt P f x`.
- "`(f, x)` is in good position" (Definition 3.53): `StrongBundle.IsGoodPositionGermSc` (germ data of
  Definition 3.11 in a tame strong bundle chart centred at `x`, `Tf̃(0)` onto `K₀`, kernel in good
  position to `C₀O` inside `T₀O` with the text's sc-complement).  This project definition states the
  kernel condition without the case distinction `d_X(x) ≥ 1`; the second conjunct of `B` is exactly
  the remark that at `d_X(x) = 0` that condition is empty (with a definition that has the case
  distinction it would be immediate).
- "`f'(x)` is surjective": `StrongBundle.IsLinSurjAt` (in some strong bundle chart around `x`, at
  the level-`1` point over `φ(x)`, `D(f̂ ∘ r)(z)|_{T_zO}` maps onto the fibre `K_z`).  The project
  records chart independence; the existential reading is the intrinsic property.
- "`∂X = ∅`": `PX.boundary = ∅` (Definition 2.25, `∂X = {x | d_X(x) ≥ 1}`).  "`d_X(x) = 0`":
  `PX.degIndex x = 0` (Definition 2.22).
- "just means": an equivalence (`↔`) between good position and surjectivity, in each case.  The
  first conjunct follows from the second (`∂X = ∅` gives `d_X(x) = 0`); both are stated, as quoted.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_100_r2
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

/-- For an sc-Fredholm section `f` of a tame strong bundle and a zero `x`: if `∂X = ∅`, `(f, x)` is
in good position iff `f'(x)` is surjective; and the same holds whenever `d_X(x) = 0` (the kernel
condition of Definition 3.53 is then empty). -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x : X),
    IsTameStrongBundle Bd → Bd.IsScFredholmSectionTame f → IsZeroAt P f x →
      (PX.boundary = ∅ → (Bd.IsGoodPositionGermSc f x ↔ Bd.IsLinSurjAt f x)) ∧
      (PX.degIndex x = 0 → (Bd.IsGoodPositionGermSc f x ↔ Bd.IsLinSurjAt f x))

end RoundTrip.V3_100_r2
