import Polyfold
/-! Blind formalization of V5_29 (the text's §5.3, Theorem 5.13, pp. 174–175).

Text: `∂X = ∅`, bump functions, `f` sc-Fredholm with compact solution set, `N` auxiliary: an open
`U ⊇ S` with `S_{f+s}` compact for `s ∈ Γ^+(P)`, `supp(s) ⊆ U`, "`N(f(x)) ≤ 1`", and a dense
`O ⊆ (Γ^{+,1}_U(P), ρ)` with `f + s` transversal for `s ∈ O`, "the germ `(f, x)` in good
position", `S_{f+s}` a compact manifold without boundary.

Choices:
- Setting: `X Y : Type` (universe 0, as asked); `PX : MPolyfold X`, `P : Y → X` with the
  fibrewise linear structure as instances on the fibres, `Bd : StrongBundle PX P`.
- Tameness: the statement as quoted does not say "tame", but the text's §5.3 works with tame
  strong bundles over tame M-polyfolds (Lemma 5.11, used to build the perturbations, assumes it,
  and "sc-Fredholm" for tame strong bundles is Definition 3.51).  I add it as a presupposed
  hypothesis: `IsTameStrongBundle Bd` below (as in `RoundTrip/Blind/V3_14.lean`: `X` tame,
  `PX.IsTame`, Definition 2.37, and an EQUIVALENT strong bundle atlas whose charts have tame base
  retractions — a property of the given structure, not "every compatible chart is tame").  With
  `∂X = ∅` this is automatic (near a point with `d = 0` every chart can be shrunk into the
  interior of its partial quadrant), so it does not weaken the claim in substance.
- `∂X = ∅`: `PX.IsWithoutBoundary` (Definition 2.25, `d_X ≡ 0`).
- "bump functions" (Definition 5.9, "`f ≠ 0` and `supp(f) ⊆ U(x)`"): read literally, `f ≠ 0`
  means `f` is not the zero function: the project's `PX.AdmitsBumpFunctionsWeak` (checked with
  `#print`: for every `x` and open `U ∋ x` an sc-smooth `f : X → ℝ`, `f ≠ 0`, `tsupport f ⊆ U`).
  Definition 5.29 says the same in words ("not identically zero").  I did NOT use the project's
  `AdmitsBumpFunctions`, which reads `f ≠ 0` as `f(x) ≠ 0` (a stronger hypothesis).
- `f` sc-Fredholm: `Bd.IsScFredholmSectionTame f` (Definition 3.51, Definition 3.14 for a tame
  strong bundle: sc-smooth, regularizing, sc-Fredholm germ data at every smooth point in a tame
  chart).  Compact solution set: `S = {x | f(x) = 0_x}` compact in `X`.
- `N` auxiliary: `Bd.IsAuxNorm N`, `N : Y[1] → ℝ` (Definition 5.1, checked).
- `Γ^+(P)`: sc⁺-sections (`IsScPlusSection`, Definition 2.52); `supp(s)` is
  `sectionSupport P s = cl{s ≠ 0}`; `N(y) ≤ 1` for `y ∈ Y` is `Bd.AuxLe N y 1` (`y ∈ Y_{0,1}` and
  `N(y) ≤ 1`, i.e. `N = ∞` off `Y_{0,1}`, the convention of Definition 5.4).
- MISPRINT 1, formalized literally: the text's condition on `s` reads "`N(f(x)) ≤ 1`" (for all
  `x`); this is evidently `N(s(x)) ≤ 1` (so that the admissible `s` form `Γ^{+,1}_U(P)`).  B
  states it literally as `∀ x, N(f(x)) ≤ 1`.
- `Γ^{+,1}_U(P)`: the project's `Bd.allowableSections N U` (checked: sc⁺-sections with
  `supp(s) ⊆ U` and `N(s(x)) ≤ 1` for all `x`).  `ρ(s, s') = sup_x N(s(x) − s'(x))`, with the
  pointwise distance the project's `sectionDistAt` (checked: `N` of the fibre difference in
  `Y_{0,1}`); "`O` dense in `(Γ^{+,1}_U(P), ρ)`": `O ⊆ Γ^{+,1}_U(P)` and every `s` there has, for
  every `δ > 0`, some `s' ∈ O` with `ρ(s, s') < δ`, written `∃ δ' < δ, ∀ x, N(s(x) − s'(x)) ≤ δ'`
  (avoids a junk supremum).
- "transversal": `Bd.IsTransversal (f + s)` (Definition 5.15, checked: at every zero the
  linearization is onto, in some strong bundle chart), `f + s` the fibrewise sum `sectionAdd`.
- MISPRINT 2, formalized literally: "the germ `(f, x)` in good position" (at every
  `x ∈ S_{f+s}`; evidently `(f + s, x)`, a restatement of transversality since `∂X = ∅`).  Good
  position of a germ is Definition 3.53, in a tame chart for a tame bundle:
  `Bd.IsGoodPositionGermTame f x`.
- "`S_{f+s}` a compact manifold without boundary": `S_{f+s}` is compact, a sub-M-polyfold
  (Definition 2.20), and its induced structure (`subPolyfold`, paracompactness asserted) has a
  compatible smooth manifold structure (`HasCornerStructure`, Definition 4.1) and no boundary
  (`IsWithoutBoundary`).
- `BIntended` is B with the two misprints corrected (`N(s(x)) ≤ 1`, the germ `(f + s, x)`); it is
  NOT the item, only an aid.
- I believe B (literal) is false in general because of misprint 2.
-/
namespace RoundTrip.V5_29
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


/-- `S` is a compact smooth manifold without boundary, as a sub-M-polyfold with its induced
structure. -/
def IsCompactManifoldWithoutBoundary (PX : MPolyfold X) (S : Set X) : Prop :=
  IsCompact S ∧ ∃ (hS : PX.IsSubMPolyfold S) (_ : ParacompactSpace S),
    (PX.subPolyfold hS).HasCornerStructure ∧ (PX.subPolyfold hS).IsWithoutBoundary

end

/-- Theorem 5.13 (literal): for an sc-Fredholm section with compact solution set over a tame
M-polyfold without boundary admitting bump functions, small perturbations supported near `S` keep
the solution set compact, and a dense set of allowable perturbations makes `f + s` transversal with
a compact solution manifold without boundary. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (N : Bd.One → ℝ),
    IsTameStrongBundle Bd → PX.IsWithoutBoundary → PX.AdmitsBumpFunctionsWeak →
    Bd.IsScFredholmSectionTame f → IsCompact (solSet P f) → Bd.IsAuxNorm N →
      ∃ U : Set X, IsOpen U ∧ solSet P f ⊆ U ∧
        -- compactness (literal: "`N(f(x)) ≤ 1`")
        (∀ s : X → Y, Bd.IsScPlusSection s → sectionSupport P s ⊆ U →
          (∀ x, Bd.AuxLe N (f x) 1) → IsCompact (solSet P (sectionAdd P f s))) ∧
        -- the dense set of good perturbations (literal: "the germ `(f, x)`")
        ∃ O : Set (X → Y), IsRhoDense Bd N (Bd.allowableSections N U) O ∧
          ∀ s ∈ O,
            Bd.IsTransversal (sectionAdd P f s) ∧
            (∀ x ∈ solSet P (sectionAdd P f s), Bd.IsGoodPositionGermTame f x) ∧
            IsCompactManifoldWithoutBoundary PX (solSet P (sectionAdd P f s))

/-- Not the item: B with the two evident misprints corrected (`N(s(x)) ≤ 1`, germ `(f + s, x)`). -/
def BIntended : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (N : Bd.One → ℝ),
    IsTameStrongBundle Bd → PX.IsWithoutBoundary → PX.AdmitsBumpFunctionsWeak →
    Bd.IsScFredholmSectionTame f → IsCompact (solSet P f) → Bd.IsAuxNorm N →
      ∃ U : Set X, IsOpen U ∧ solSet P f ⊆ U ∧
        (∀ s : X → Y, Bd.IsScPlusSection s → sectionSupport P s ⊆ U →
          (∀ x, Bd.AuxLe N (s x) 1) → IsCompact (solSet P (sectionAdd P f s))) ∧
        ∃ O : Set (X → Y), IsRhoDense Bd N (Bd.allowableSections N U) O ∧
          ∀ s ∈ O,
            Bd.IsTransversal (sectionAdd P f s) ∧
            (∀ x ∈ solSet P (sectionAdd P f s), Bd.IsGoodPositionGermTame (sectionAdd P f s) x) ∧
            IsCompactManifoldWithoutBoundary PX (solSet P (sectionAdd P f s))

end RoundTrip.V5_29
