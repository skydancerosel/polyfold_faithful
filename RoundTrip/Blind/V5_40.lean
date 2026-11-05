import Polyfold
/-! Blind formalization of V5_40 (the text's §5.3, Theorem 5.19, p. 180).

Text: over a tame `X` with bump functions, `f` sc-Fredholm with compact solution set, `(f, x)` in
good position at the zeros on `∂X`: `U` with `S_{f+s}` compact for `s ∈ Γ^{+,1}_U(P)`, and an
arbitrarily small `s ∈ Γ^{+,1}_U(P)` with `s = 0` near `∂X`, `f + s` transversal, "`(f, x)`" in
good position at every `x ∈ S_{f+s}`, `S_{f+s}` a compact manifold with boundary with corners.

Choices:
- Setting: `X Y : Type` (universe 0, as asked); `PX : MPolyfold X`, `P : Y → X` with the
  fibrewise linear structure as instances on the fibres, `Bd : StrongBundle PX P`.
- "Over a tame `X`": as in `RoundTrip/Blind/V5_29.lean` / `V5_38.lean`, the tame setting of §5.3
  (Lemma 5.11; good position, Definition 3.53, is a notion for tame strong bundles, §3.6):
  `IsTameStrongBundle Bd` (`PX.IsTame`, Definition 2.37, and an EQUIVALENT strong bundle atlas
  whose charts have tame base retractions — a property of the given structure), and `f`
  sc-Fredholm in the tame sense `Bd.IsScFredholmSectionTame f` (Definition 3.51).
- "bump functions" (Definition 5.9, "`f ≠ 0`"; Definition 5.29: "not identically zero"): the
  literal reading, the project's `PX.AdmitsBumpFunctionsWeak` (checked: `f ≠ 0` as a function).
  NOT `AdmitsBumpFunctions` (`f(x) ≠ 0`, a stronger hypothesis).
- Compact solution set: `S = {x | f(x) = 0_x}` compact in `X`.
- `N`: not named in the quoted statement, but `Γ^{+,1}_U(P)` and its smallness are relative to an
  auxiliary norm; as in Theorems 5.13, 5.18, B quantifies over every auxiliary norm `N`
  (`Bd.IsAuxNorm N`, Definition 5.1).
- "`(f, x)` in good position at the zeros on `∂X`": for every `x ∈ S` with `x ∈ ∂X`
  (`PX.boundary = {d_X ≥ 1}`, Definition 2.25), `Bd.IsGoodPositionGermTame f x` (Definition 3.53
  in a tame chart, the project's, checked with `#print`: sc-Fredholm germ data in a tame strong
  bundle chart centred at `x` whose filled version is in good position, `IsGoodPositionAt`).
- `U`: existential, "there is an open `U ⊇ S` with `S_{f+s}` compact for every
  `s ∈ Γ^{+,1}_U(P)`" (the project's `Bd.allowableSections N U`, checked: sc⁺-sections `s` with
  `cl{s ≠ 0} ⊆ U` and `N(s(x)) ≤ 1` for all `x`).
- "an arbitrarily small `s ∈ Γ^{+,1}_U(P)`": for every `ε > 0` there is such an `s` with
  `ρ(s, 0) = sup_x N(s(x)) < ε`, written `∃ δ < ε, ∀ x, N(s(x)) ≤ δ` (`AuxLe`; `s(x) ∈ Y_{0,1}`
  holds anyway).  "`s = 0` near `∂X`": there is an open `W ⊇ ∂X` with `s(x) = 0_x` on `W`.
- "`f + s` transversal": `Bd.IsTransversal (f + s)` (Definition 5.15), `f + s` the fibrewise sum
  `sectionAdd`.
- MISPRINT, formalized literally: the text writes "`(f, x)`" in good position at every
  `x ∈ S_{f+s}`; this is evidently `(f + s, x)`.  B states it literally:
  `Bd.IsGoodPositionGermTame f x` for `x ∈ S_{f+s}`.  `BIntended` (NOT the item, only an aid) has
  `(f + s, x)`.  I believe the literal B is false: for `f ≡ 0` in the Möbius line bundle over the
  circle every small `s` has a zero `x`, and there `(f, x) = (0, x)` is not in good position
  (`f'(x) = 0` is not onto, clause (1) of `IsGoodPositionAt`).
- "`S_{f+s}` a compact manifold with boundary with corners": `S_{f+s}` compact, a sub-M-polyfold
  (Definition 2.20) whose induced structure (`subPolyfold`, paracompactness asserted) has a
  compatible manifold-with-corners structure (`HasCornerStructure`, Definition 4.1).
-/
namespace RoundTrip.V5_40
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

/-- `S` is a compact manifold with boundary with corners, as a sub-M-polyfold with its induced
structure. -/
def IsCompactCornerManifold (PX : MPolyfold X) (S : Set X) : Prop :=
  IsCompact S ∧ ∃ (hS : PX.IsSubMPolyfold S) (_ : ParacompactSpace S),
    (PX.subPolyfold hS).HasCornerStructure

end

/-- Theorem 5.19 (literal): over a tame M-polyfold with bump functions, an sc-Fredholm section
with compact solution set, in good position at its boundary zeros, admits an open `U ⊇ S` with
`S_{f+s}` compact for `s ∈ Γ^{+,1}_U(P)`, and arbitrarily small `s ∈ Γ^{+,1}_U(P)` vanishing near
`∂X` with `f + s` transversal, "`(f, x)`" in good position on `S_{f+s}`, and `S_{f+s}` a compact
manifold with boundary with corners. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (N : Bd.One → ℝ),
    IsTameStrongBundle Bd → PX.AdmitsBumpFunctionsWeak →
    Bd.IsScFredholmSectionTame f → IsCompact (solSet P f) → Bd.IsAuxNorm N →
    (∀ x ∈ solSet P f, x ∈ PX.boundary → Bd.IsGoodPositionGermTame f x) →
      ∃ U : Set X, IsOpen U ∧ solSet P f ⊆ U ∧
        (∀ s ∈ Bd.allowableSections N U, IsCompact (solSet P (sectionAdd P f s))) ∧
        ∀ ε : ℝ, 0 < ε → ∃ s ∈ Bd.allowableSections N U,
          (∃ δ < ε, ∀ x, Bd.AuxLe N (s x) δ) ∧
          (∃ W : Set X, IsOpen W ∧ PX.boundary ⊆ W ∧ ∀ x ∈ W, IsZeroAt P s x) ∧
          Bd.IsTransversal (sectionAdd P f s) ∧
          -- literal: "`(f, x)`" (evidently `(f + s, x)`)
          (∀ x ∈ solSet P (sectionAdd P f s), Bd.IsGoodPositionGermTame f x) ∧
          IsCompactCornerManifold PX (solSet P (sectionAdd P f s))

/-- Not the item: B with the evident misprint corrected (`(f + s, x)` in good position). -/
def BIntended : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (N : Bd.One → ℝ),
    IsTameStrongBundle Bd → PX.AdmitsBumpFunctionsWeak →
    Bd.IsScFredholmSectionTame f → IsCompact (solSet P f) → Bd.IsAuxNorm N →
    (∀ x ∈ solSet P f, x ∈ PX.boundary → Bd.IsGoodPositionGermTame f x) →
      ∃ U : Set X, IsOpen U ∧ solSet P f ⊆ U ∧
        (∀ s ∈ Bd.allowableSections N U, IsCompact (solSet P (sectionAdd P f s))) ∧
        ∀ ε : ℝ, 0 < ε → ∃ s ∈ Bd.allowableSections N U,
          (∃ δ < ε, ∀ x, Bd.AuxLe N (s x) δ) ∧
          (∃ W : Set X, IsOpen W ∧ PX.boundary ⊆ W ∧ ∀ x ∈ W, IsZeroAt P s x) ∧
          Bd.IsTransversal (sectionAdd P f s) ∧
          (∀ x ∈ solSet P (sectionAdd P f s), Bd.IsGoodPositionGermTame (sectionAdd P f s) x) ∧
          IsCompactCornerManifold PX (solSet P (sectionAdd P f s))

end RoundTrip.V5_40
