import Polyfold
/-! Blind formalization of V5_39 (the text's §5.3, Theorem 5.18, p. 177, its dense form).

Text: "There exists a dense subset `O` of the metric space `(Γ^{+,1}_U(P), ρ)` such that, for every
`s ∈ O`," `(f + s, x)` is in general position at every zero.  The setting is that of Theorem 5.18
(blind statement V5_38, `RoundTrip/Blind/V5_38.lean`): sc-smooth bump functions, `f` sc-Fredholm
with compact solution set `S`, `N` an auxiliary norm, `U` the open neighbourhood of `S` given by
the theorem, with `S_{f+s}` compact for `s ∈ Γ^{+,1}_U(P)`.

Choices:
- Setting: `X Y : Type` (universe 0, as asked); `PX : MPolyfold X`, `P : Y → X` with the
  fibrewise linear structure as instances on the fibres, `Bd : StrongBundle PX P`.
- Tameness: not in the quoted statement, but clearly presupposed: general position (Definition
  5.17) is stated with the reduced tangent space `T^R_xX` of a tame M-polyfold, in a tame chart,
  and §5.3 works with tame strong bundles (Lemma 5.11).  As in V5_38: hypothesis
  `IsTameStrongBundle Bd` (`PX.IsTame`, Definition 2.37, and an EQUIVALENT strong bundle atlas
  whose charts have tame base retractions — a property of the given structure, not "every chart is
  tame"), and `f` sc-Fredholm in the tame sense, `Bd.IsScFredholmSectionTame f` (Definition 3.51:
  sc-Fredholm germ data in tame charts).
- "bump functions" (Definition 5.9, "`f ≠ 0` and `supp(f) ⊆ U(x)`"; Definition 5.29: "not
  identically zero"): the literal reading, the project's `PX.AdmitsBumpFunctionsWeak` (checked:
  `f ≠ 0` as a function).  NOT `AdmitsBumpFunctions` (`f(x) ≠ 0`, a stronger hypothesis).
- Compact solution set: `S = {x | f(x) = 0_x}` compact in `X`.  `N`: `Bd.IsAuxNorm N`
  (Definition 5.1).
- `U`: the open neighbourhood of `S` of the theorem: B says "there is an open `U ⊇ S` with
  `S_{f+s}` compact for every `s ∈ Γ^{+,1}_U(P)` and a dense `O ⊆ (Γ^{+,1}_U(P), ρ)` …" (the
  compactness property is what makes `U` the `U` of the theorem).
- `Γ^{+,1}_U(P)`: the project's `Bd.allowableSections N U` (checked: sc⁺-sections `s` with
  `cl{s ≠ 0} ⊆ U` and `N(s(x)) ≤ 1` for all `x`).  `ρ(s, s') = sup_x N(s(x) − s'(x))`, pointwise
  the project's `sectionDistAt` (checked); "dense": `O ⊆ Γ^{+,1}_U(P)` and every `s` there has,
  for every `δ > 0`, an `s' ∈ O` with `ρ(s, s') < δ` (`∃ δ' < δ, ∀ x, … ≤ δ'`).  As in V5_38.
- "`(f + s, x)` is in general position at every zero": for every `x` with `(f + s)(x) = 0_x`,
  `Bd.IsGeneralPositionGerm (f + s) x` (Definition 5.17, the project's, as in V5_38: in some tame
  strong bundle chart the linearization is onto and its kernel has an sc-complement inside the
  reduced tangent space), `f + s` the fibrewise sum `sectionAdd`.
- Nothing looks false to me (apart from the reading of "bump functions", see above).
-/
namespace RoundTrip.V5_39
open Polyfold

/-- The solution set `S_g = {x | g(x) = 0_x}`. -/
def solSet {X Y : Type} (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] (g : X → Y) : Set X :=
  {x | IsZeroAt P g x}

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- A **tame strong bundle**: tame base, and an equivalent strong bundle atlas of charts whose base
retractions are tame. -/
def IsTameStrongBundle (Bd : StrongBundle PX P) : Prop :=
  PX.IsTame ∧ ∃ A : StrongBundleAtlas PX P, A.Equiv Bd.atlas ∧
    ∀ c ∈ A.charts, (IsStrongBundleRetraction.baseRetraction c.relOpen c.isRetraction).IsTame

/-- `ρ(s, s') < δ`, `ρ(s, s') = sup_x N(s(x) − s'(x))`. -/
def RhoLt (Bd : StrongBundle PX P) (N : Bd.One → ℝ) (s s' : X → Y) (δ : ℝ) : Prop :=
  ∃ (hs : Bd.IsScPlusSection s) (hs' : Bd.IsScPlusSection s'),
    ∃ δ' < δ, ∀ x, Bd.sectionDistAt N hs hs' x ≤ δ'

/-- `O` is a dense subset of the metric space `(Γ, ρ)`. -/
def IsRhoDense (Bd : StrongBundle PX P) (N : Bd.One → ℝ) (Γ O : Set (X → Y)) : Prop :=
  O ⊆ Γ ∧ ∀ s ∈ Γ, ∀ δ > 0, ∃ s' ∈ O, RhoLt Bd N s s' δ

end

/-- Theorem 5.18, dense form: there is an open `U ⊇ S` with `S_{f+s}` compact for
`s ∈ Γ^{+,1}_U(P)`, and a `ρ`-dense set of `s ∈ Γ^{+,1}_U(P)` for which `(f + s, x)` is in general
position at every zero `x` of `f + s`. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (N : Bd.One → ℝ),
    IsTameStrongBundle Bd → PX.AdmitsBumpFunctionsWeak →
    Bd.IsScFredholmSectionTame f → IsCompact (solSet P f) → Bd.IsAuxNorm N →
      ∃ U : Set X, IsOpen U ∧ solSet P f ⊆ U ∧
        (∀ s ∈ Bd.allowableSections N U, IsCompact (solSet P (sectionAdd P f s))) ∧
        ∃ O : Set (X → Y), IsRhoDense Bd N (Bd.allowableSections N U) O ∧
          ∀ s ∈ O, ∀ x ∈ solSet P (sectionAdd P f s),
            Bd.IsGeneralPositionGerm (sectionAdd P f s) x

end RoundTrip.V5_39
