import Polyfold
/-! Blind formalization of V5_20 (the text's §5.3, Lemma 5.11, p. 173).

Text: for a tame strong bundle over a tame `X` with sc-smooth bump functions, an auxiliary norm
`N`, smooth `x`, smooth `e ∈ Y_x`, `ε > 0` and open `U ∋ x`: an `s ∈ Γ⁺(P)` with `s(x) = e`,
`supp(s) ⊆ U`, `N(s(x)) < N(e) + ε`.

Choices:
- Setting: `X Y : Type` (universe 0, as asked); `PX : MPolyfold X`, `P : Y → X` with the
  fibrewise linear structure as instances on the fibres, `Bd : StrongBundle PX P`.
- "tame strong bundle over a tame `X`": `IsTameStrongBundle Bd` (the prelude of
  `RoundTrip/Blind/V5_29.lean`): `PX.IsTame` (Definition 2.37, an EQUIVALENT atlas of tame charts,
  checked with `#print`) and an EQUIVALENT strong bundle atlas whose charts have tame base
  retractions (Definition 2.34) — a property of the given structure, not "every compatible chart
  is tame".
- "with sc-smooth bump functions": Definition 5.9 read literally (`f` not identically zero), the
  project's `PX.AdmitsBumpFunctionsWeak` (checked with `#print`; see `RoundTrip/Blind/V5_16.lean`).
  Not the project's stronger `AdmitsBumpFunctions` (`f(x) ≠ 0`).
- "auxiliary norm": the project's `Bd.IsAuxNorm N`, `N : Y_{0,1} → ℝ` (`Bd.One`) (Definition 5.1,
  checked; compared with the text in `RoundTrip/Blind/V5_3.lean`).
- "smooth `x`": `x ∈ X_∞` (`PX.smoothSet`).  "smooth `e ∈ Y_x`": `e ∈ P⁻¹(x)` lying in every
  `Y_{m,m}` (`Bd.doubleLevel m m`, checked: base component in `E_m`, fibre component in `F_m` in
  the charts of the atlas), i.e. a smooth point of `Y`; such an `e` lies in `Y_{0,1}`, so `e` is
  taken in `Bd.One` (needed to write `N(e)`).
- "`s ∈ Γ⁺(P)`": `Bd.IsScPlusSection s` (Definition 2.52, checked).  "`supp(s)`": the project's
  `sectionSupport P s` (checked: `cl{x | s(x) ≠ 0_x}`).
- `N(y) < r` for `y ∈ Y`: `y ∈ Y_{0,1}` and `N(y) < r` (`NLt`).
- MISPRINT (formalized literally): "`N(s(x)) < N(e) + ε`" with `x` the given point is implied by
  `s(x) = e`, so the conjunct is vacuous; surely the text means `N(s(y)) < N(e) + ε` for ALL
  `y ∈ X` (a small sup-norm, needed for `Γ^{+,1}_U(P)`).  B states it literally, at the given `x`;
  `BIntended` (not the item) states it for all `y`.
- DOUBT: under the literal ("not identically zero") reading of the bump-function hypothesis I am
  not sure the lemma follows (a cut-off equal to `1` at `x` is presumably needed); see
  `RoundTrip/Blind/V5_17.lean`.
-/
namespace RoundTrip.V5_20
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- A **tame strong bundle** over a tame M-polyfold: tame base, and an equivalent strong bundle
atlas of charts whose base retractions are tame. -/
def IsTameStrongBundle (Bd : StrongBundle PX P) : Prop :=
  PX.IsTame ∧ ∃ A : StrongBundleAtlas PX P, A.Equiv Bd.atlas ∧
    ∀ c ∈ A.charts, (IsStrongBundleRetraction.baseRetraction c.relOpen c.isRetraction).IsTame

/-- `N(y) < r`, with `N(y) = ∞` for `y ∉ Y_{0,1}`. -/
def NLt (Bd : StrongBundle PX P) (N : Bd.One → ℝ) (y : Y) (r : ℝ) : Prop :=
  ∃ hy : y ∈ Bd.oneSet, N ⟨y, hy⟩ < r

end

/-- Lemma 5.11 (literal): a smooth vector `e` over a smooth point `x` extends to an sc⁺-section
supported in a given neighbourhood of `x` (with the norm condition read at `x`). -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (N : Bd.One → ℝ),
    IsTameStrongBundle Bd → PX.AdmitsBumpFunctionsWeak → Bd.IsAuxNorm N →
    ∀ x ∈ PX.smoothSet, ∀ e : Bd.One, P (Bd.oneVal e) = x →
      (∀ m : ℕ, Bd.oneVal e ∈ Bd.doubleLevel m m) →
      ∀ ε : ℝ, 0 < ε → ∀ U : Set X, IsOpen U → x ∈ U →
        ∃ s : X → Y, Bd.IsScPlusSection s ∧ s x = Bd.oneVal e ∧ sectionSupport P s ⊆ U ∧
          NLt Bd N (s x) (N e + ε)

/-- Not the item: Lemma 5.11 with the evident reading `N(s(y)) < N(e) + ε` for all `y`. -/
def BIntended : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (N : Bd.One → ℝ),
    IsTameStrongBundle Bd → PX.AdmitsBumpFunctionsWeak → Bd.IsAuxNorm N →
    ∀ x ∈ PX.smoothSet, ∀ e : Bd.One, P (Bd.oneVal e) = x →
      (∀ m : ℕ, Bd.oneVal e ∈ Bd.doubleLevel m m) →
      ∀ ε : ℝ, 0 < ε → ∀ U : Set X, IsOpen U → x ∈ U →
        ∃ s : X → Y, Bd.IsScPlusSection s ∧ s x = Bd.oneVal e ∧ sectionSupport P s ⊆ U ∧
          ∀ y : X, NLt Bd N (s y) (N e + ε)

end RoundTrip.V5_20
