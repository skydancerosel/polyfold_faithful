import Polyfold
/-! Blind formalization of V5_41 (the text's §5.3, Definition 5.20, pp. 180–181).

Text: a generalized compact homotopy (between the compact sc-Fredholm problems `(f₀, P₀)` and
`(f₁, P₁)`) consists of a tame strong bundle `P : Y → X`, an sc-Fredholm section `f` of `P` with
compact solution set and an sc-smooth surjective `t : X → [0, 1]` such that the `X_t = t⁻¹(t)` are
tame M-polyfolds, `f_t = f|X_t` are sc-Fredholm sections of `Y|X_t`, and
`(f|X_i, P|Y_i) = (f_i, P_i)` for `i = 0, 1`.

Choices:
- This item is a definition.  B says that the project's `Bd.IsGenCompactHomotopy f t` (Definition
  5.20) is the text's notion `IsGenCompactHomotopyB Bd f t` written below.
- Setting: `X Y : Type` (universe 0, as asked); `PX : MPolyfold X`, `P : Y → X` with the
  fibrewise linear structure as instances on the fibres, `Bd : StrongBundle PX P`, as in
  `RoundTrip/Blind/V5_38.lean`.
- "a tame strong bundle `P : Y → X`": `IsTameStrongBundle Bd` (as in `RoundTrip/Blind/V3_14.lean`,
  `V5_38.lean`: `X` tame, `PX.IsTame`, Definition 2.37, and an EQUIVALENT strong bundle atlas whose
  charts have tame base retractions — a property of the given structure, not "every compatible
  chart is tame").
- "an sc-Fredholm `f`": for a tame strong bundle the text's sc-Fredholm notion is Definition 3.51
  (Definition 3.14 with the germ data in tame charts), the project's
  `Bd.IsScFredholmSectionTame f` (as in V5_38).  "compact solution set": `{x | f(x) = 0_x}`
  compact in `X`.
- "an sc-smooth surjective `t : X → [0, 1]`": `t : X → ℝ` sc-smooth for the one-chart
  M-polyfold structure of `ℝ` (`PX.IsScSmoothMap realPolyfold t`, Definition 2.14 /
  `realPolyfold`, checked) with `t(X) = [0, 1]`.
- "`X_t` tame M-polyfolds": for every `τ ∈ [0, 1]`, `X_τ = t⁻¹(τ)` is a sub-M-polyfold of `X`
  (Definition 2.20, `PX.IsSubMPolyfold`) — the M-polyfold structure the text means on the subset
  `X_τ` is the induced one (`subPolyfold`, Proposition 2.21; its paracompactness hypothesis is
  existentially quantified, it is a `Prop`) — and that induced structure is tame (`IsTame`).
- "`f_t = f|X_t` sc-Fredholm sections of `Y|X_t`": `Y|X_τ` is the pull-back `ι*Y → X_τ` of `P`
  along the inclusion `ι : X_τ → X` (the project's `StrongBundle.pullback`, Proposition 2.54, for
  `ι` sc-smooth — I ask for a proof of this as part of the condition), and `f|X_τ` is the section
  `a ↦ (a, f(a))` (`restrictSection`, checked: needs `f` to be a section).  "sc-Fredholm": as for
  `f`, in the tame sense (`IsScFredholmSectionTame`) — `Y|X_τ` lives over the tame `X_τ`.  (The
  plain Definition 3.14 would be the other possible reading.)
- "`(f|X_i, P|Y_i) = (f_i, P_i)`": I read it as naming the end problems — the compact
  sc-Fredholm problems at the two ends ARE the restrictions to `X_0 = t⁻¹(0)` and `X_1 = t⁻¹(1)`
  — so the notion is a property of `(P, f, t)`; the restrictions are covered by the `τ = 0, 1`
  cases above (their solution sets are closed in the compact `f⁻¹(0)`).  A version "between given
  problems `(f_i, P_i)`" would need an isomorphism of strong bundles with sections between
  `(f|X_i, ι_i*Y)` and `(f_i, P_i)`, which neither the vocabulary nor this file formalizes.
- Nothing looks false to me.
-/
namespace RoundTrip.V5_41
open Polyfold

/-- The solution set `S_g = {x | g(x) = 0_x}`. -/
def solSet {X Y : Type} (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] (g : X → Y) : Set X :=
  {x | g x = ((0 : P ⁻¹' {x}) : Y)}

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- A **tame strong bundle**: tame base, and an equivalent strong bundle atlas of charts whose base
retractions are tame. -/
def IsTameStrongBundle (Bd : StrongBundle PX P) : Prop :=
  PX.IsTame ∧ ∃ A : StrongBundleAtlas PX P, A.Equiv Bd.atlas ∧
    ∀ c ∈ A.charts, (IsStrongBundleRetraction.baseRetraction c.relOpen c.isRetraction).IsTame

/-- The level set `X_τ = t⁻¹(τ)` is a tame M-polyfold (a sub-M-polyfold with tame induced
structure) and `f|X_τ` is an sc-Fredholm section of `Y|X_τ = ι*Y`. -/
def FibreCondition (Bd : StrongBundle PX P) (f : X → Y) (t : X → ℝ) (τ : ℝ) : Prop :=
  ∃ (hsub : PX.IsSubMPolyfold (t ⁻¹' {τ})) (_ : ParacompactSpace (t ⁻¹' {τ})),
    (PX.subPolyfold hsub).IsTame ∧
    ∃ (hι : (PX.subPolyfold hsub).IsScSmoothMap PX (Subtype.val : t ⁻¹' {τ} → X))
      (_ : ParacompactSpace (pullbackSpace P (Subtype.val : t ⁻¹' {τ} → X)))
      (hf : IsSection P f),
      (Bd.pullback hι).IsScFredholmSectionTame (restrictSection P (t ⁻¹' {τ}) f hf)

/-- **Definition 5.20**: `(P, f, t)` is a generalized compact homotopy. -/
def IsGenCompactHomotopyB (Bd : StrongBundle PX P) (f : X → Y) (t : X → ℝ) : Prop :=
  IsTameStrongBundle Bd ∧
  Bd.IsScFredholmSectionTame f ∧ IsCompact (solSet P f) ∧
  PX.IsScSmoothMap realPolyfold t ∧ Set.range t = Set.Icc 0 1 ∧
  ∀ τ ∈ Set.Icc (0 : ℝ) 1, FibreCondition Bd f t τ

end

/-- Definition 5.20: the project's generalized compact homotopies are the text's. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (t : X → ℝ),
    Bd.IsGenCompactHomotopy f t ↔ IsGenCompactHomotopyB Bd f t

end RoundTrip.V5_41
