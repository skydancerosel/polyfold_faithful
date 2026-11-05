import Polyfold
/-! Blind formalization of V5_38 (the text's §5.3, Theorem 5.18, p. 177).

Text: bump functions, `f` sc-Fredholm with compact solution set, `N` auxiliary: an open `U ⊇ S`
with `S_{f+s}` compact for `s ∈ Γ^{+,1}_U(P)`, and a dense `O ⊆ (Γ^{+,1}_U(P), ρ)` such that for
`s ∈ O`, `(f + s, x)` is in general position at every `x ∈ S_{f+s}`; `S_{f+s}` is a compact
manifold with boundary with corners, `d_{S_{f+s}} = d_X`.

Choices:
- Setting: `X Y : Type` (universe 0, as asked); `PX : MPolyfold X`, `P : Y → X` with the
  fibrewise linear structure as instances on the fibres, `Bd : StrongBundle PX P`.
- Tameness: not in the quoted statement, but clearly presupposed: general position (Definition
  5.17) is stated with the reduced tangent space `T^R_xX` of a tame M-polyfold, in a tame chart,
  and §5.3 works with tame strong bundles (Lemma 5.11).  Hypothesis `IsTameStrongBundle Bd` (as in
  `RoundTrip/Blind/V3_14.lean`: `PX.IsTame`, Definition 2.37, and an EQUIVALENT strong bundle atlas
  whose charts have tame base retractions — a property of the given structure).
- "bump functions" (Definition 5.9, "`f ≠ 0` and `supp(f) ⊆ U(x)`"): read literally, `f` is not
  the zero function: the project's `PX.AdmitsBumpFunctionsWeak` (checked with `#print`).  I did NOT
  use `AdmitsBumpFunctions`, which reads `f ≠ 0` as `f(x) ≠ 0` (a stronger hypothesis).
- `f` sc-Fredholm: `Bd.IsScFredholmSectionTame f` (Definition 3.51, sc-Fredholm germ data in tame
  charts).  Compact solution set: `S = {x | f(x) = 0_x}` compact in `X`.  `N`: `Bd.IsAuxNorm N`
  (Definition 5.1).
- `Γ^{+,1}_U(P)`: the project's `Bd.allowableSections N U` (checked: sc⁺-sections `s` with
  `cl{s ≠ 0} ⊆ U` and `N(s(x)) ≤ 1` for all `x`).  `ρ(s, s') = sup_x N(s(x) − s'(x))` with the
  pointwise distance `sectionDistAt` (checked); "dense": `O ⊆ Γ^{+,1}_U(P)` and every `s` there
  has, for every `δ > 0`, an `s' ∈ O` with `ρ(s, s') < δ` (`∃ δ' < δ, ∀ x, … ≤ δ'`).
- "`(f + s, x)` is in general position": `Bd.IsGeneralPositionGerm (f + s) x` (Definition 5.17,
  checked: in some tame strong bundle chart around `x`, at the level-`1` lift `z`, the
  linearization `T_zO → K_z` is onto and, for every presentation of the partial quadrant, its
  kernel has an sc-complement in `T_zO` contained in `T^R_zO`), with `f + s` the fibrewise sum
  `sectionAdd`.
- "`S_{f+s}` is a compact manifold with boundary with corners, `d_{S_{f+s}} = d_X`": `S_{f+s}` is
  compact, a sub-M-polyfold (Definition 2.20) whose induced structure (`subPolyfold`,
  paracompactness asserted) has a compatible corner structure (`HasCornerStructure`, Definition
  4.1), and the degeneracy index of the induced structure equals `d_X` on `S_{f+s}`.
- Nothing looks false to me (apart from the reading of "bump functions", see above).
-/
namespace RoundTrip.V5_38
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

/-- Theorem 5.18: allowable perturbations supported near `S` keep the solution set compact, and a
dense set of them puts `f + s` in general position at every zero, with a compact solution set
which is a manifold with boundary with corners whose degeneracy index is that of `X`. -/
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
          ∀ s ∈ O,
            (∀ x ∈ solSet P (sectionAdd P f s), Bd.IsGeneralPositionGerm (sectionAdd P f s) x) ∧
            IsCompact (solSet P (sectionAdd P f s)) ∧
            ∃ (hS : PX.IsSubMPolyfold (solSet P (sectionAdd P f s)))
              (_ : ParacompactSpace (solSet P (sectionAdd P f s))),
              (PX.subPolyfold hS).HasCornerStructure ∧
              ∀ x : solSet P (sectionAdd P f s), (PX.subPolyfold hS).degIndex x = PX.degIndex x

end RoundTrip.V5_38
