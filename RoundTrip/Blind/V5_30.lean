import Polyfold
/-! Blind formalization of V5_30 (the text's §5.3, Theorem 5.13, pp. 174–175, its dense form).

Text: "There exists a dense subset `O` of the metric space `(Γ^{+,1}_U(P), ρ)` such that for every
`s ∈ O`" `f + s` is transversal and `S_{f+s}` is a compact manifold without boundary.  The setting
is that of Theorem 5.13 (see `RoundTrip/Blind/V5_29.lean` and the blind statement V5_29):
`∂X = ∅`, sc-smooth bump functions, `f` sc-Fredholm with compact solution set `S`, `N` an
auxiliary norm, `U` the open neighbourhood of `S` given by the theorem.

Choices:
- Setting: `X Y : Type` (universe 0, as asked); `PX : MPolyfold X`, `P : Y → X` with the
  fibrewise linear structure as instances on the fibres, `Bd : StrongBundle PX P`.
- Hypotheses of Theorem 5.13, as the text lists them: `∂X = ∅` (`PX.IsWithoutBoundary`,
  Definition 2.25, `d_X ≡ 0`); bump functions; `f` sc-Fredholm with compact solution set; `N`
  auxiliary.
- NO TAMENESS: Theorem 5.13 does not say "tame" and nothing in this claim (transversality,
  manifold without boundary) involves tame notions; with `∂X = ∅` tameness is automatic in
  substance anyway.  So, unlike `RoundTrip/Blind/V5_29.lean` (which added a tame strong bundle and
  the tame-chart Fredholm notion), I assume neither: `f` sc-Fredholm is the project's
  `Bd.IsScFredholmSection f` (Definition 3.14, checked with `#print`).
- "bump functions" (Definition 5.9, "`f ≠ 0` and `supp(f) ⊆ U(x)`"; Definition 5.29: "not
  identically zero"): the literal reading, the project's `PX.AdmitsBumpFunctionsWeak` (checked:
  `f` sc-smooth, `f ≠ 0` as a function, `tsupport f ⊆ U`), as in V5_29 / V5_38.  NOT the project's
  `AdmitsBumpFunctions`, which reads `f ≠ 0` as `f(x) ≠ 0`.
- `S_g = {x | g(x) = 0_x}`; compact solution set: `S_f` compact in `X`.  `N`: `Bd.IsAuxNorm N`
  (Definition 5.1).
- `U`: the open neighbourhood of `S` of the theorem, i.e. B says "there is an open `U ⊇ S` such
  that `S_{f+s}` is compact for `s ∈ Γ^{+,1}_U(P)` and there is a dense `O ⊆ (Γ^{+,1}_U(P), ρ)`
  …".  The compactness property is what makes `U` "the `U` of the theorem"; I state it for
  `s ∈ Γ^{+,1}_U(P)` (the reading of Theorems 5.18, 5.19, 5.25 and Remark 5.12).  The text's
  Theorem 5.13 writes that condition with the misprint "`N(f(x)) ≤ 1`" (formalized literally in
  V5_29); the quoted dense form does not contain it.
- `Γ^{+,1}_U(P)`: the project's `Bd.allowableSections N U` (checked: sc⁺-sections `s` with
  `cl{s ≠ 0} ⊆ U` and `N(s(x)) ≤ 1` for all `x`).  `ρ(s, s') = sup_x N(s(x) − s'(x))`, pointwise
  the project's `sectionDistAt` (checked); "`O` dense": `O ⊆ Γ^{+,1}_U(P)` and every `s` there has,
  for every `δ > 0`, an `s' ∈ O` with `ρ(s, s') < δ` (`∃ δ' < δ, ∀ x, … ≤ δ'`, no junk supremum).
  Same definitions as V5_29.
- "`f + s` transversal": `Bd.IsTransversal (f + s)` (Definition 5.15, checked: at every zero the
  linearization is onto), `f + s` the fibrewise sum `sectionAdd`.
- "`S_{f+s}` a compact manifold without boundary": compact, a sub-M-polyfold (Definition 2.20)
  whose induced structure (`subPolyfold`, paracompactness asserted) has a compatible smooth
  manifold structure (`HasCornerStructure`, Definition 4.1) and no boundary
  (`IsWithoutBoundary`) — V5_29's `IsCompactManifoldWithoutBoundary`.
- Nothing looks false to me.
-/
namespace RoundTrip.V5_30
open Polyfold

/-- The solution set `S_g = {x | g(x) = 0_x}`. -/
def solSet {X Y : Type} (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] (g : X → Y) : Set X :=
  {x | IsZeroAt P g x}

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

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

/-- Theorem 5.13, dense form: over an M-polyfold without boundary admitting bump functions, for an
sc-Fredholm section with compact solution set and an auxiliary norm there is an open `U ⊇ S` with
`S_{f+s}` compact for `s ∈ Γ^{+,1}_U(P)`, and a `ρ`-dense set of `s ∈ Γ^{+,1}_U(P)` for which
`f + s` is transversal with a compact solution manifold without boundary. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (N : Bd.One → ℝ),
    PX.IsWithoutBoundary → PX.AdmitsBumpFunctionsWeak →
    Bd.IsScFredholmSection f → IsCompact (solSet P f) → Bd.IsAuxNorm N →
      ∃ U : Set X, IsOpen U ∧ solSet P f ⊆ U ∧
        (∀ s ∈ Bd.allowableSections N U, IsCompact (solSet P (sectionAdd P f s))) ∧
        ∃ O : Set (X → Y), IsRhoDense Bd N (Bd.allowableSections N U) O ∧
          ∀ s ∈ O,
            Bd.IsTransversal (sectionAdd P f s) ∧
            IsCompactManifoldWithoutBoundary PX (solSet P (sectionAdd P f s))

end RoundTrip.V5_30
