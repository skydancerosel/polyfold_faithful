import Polyfold
/-! Blind formalization of V5_45 (the text's §5.3, Theorem 5.25, pp. 186–187).

Text: over a tame `X` with bump functions, `f` proper sc-Fredholm, `N` auxiliary and "an
associated open neighborhood `U`" with `S_{f+s}` compact for `s ∈ Γ^{+,1}_U(P)`: some
`s ∈ Γ^{+,1}_U(P)` puts `(f + s, x)` in good position at every `x ∈ S_{f+s}`; `S_{f+s}` is a
manifold with boundary with corners.

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
- "proper": the project's `Bd.IsProper f` (Definition 5.4 (3), checked with `#print`: compact
  solution set, and for every auxiliary `N` an open `U ⊇ f⁻¹(0)` with `cl{x ∈ U | N(f(x)) ≤ 1}`
  compact).  `N`: `Bd.IsAuxNorm N` (Definition 5.1).
- "an associated open neighborhood `U` with `S_{f+s}` compact for `s ∈ Γ^{+,1}_U(P)`": `U` is
  universally quantified, an open set containing `S = f⁻¹(0)` with `S_{f+s}` compact for every
  `s ∈ Γ^{+,1}_U(P)` (the property the text attaches to `U`; it is the neighbourhood of
  Definition 5.4 (2) for `N`, `{f = −s} = S_{f+s}`).  I did NOT read "associated" as "the
  neighbourhood of Definition 5.4 (3)" (`cl{x ∈ U | N(f(x)) ≤ 1}` compact), which would be a
  stronger hypothesis on `U` (it implies the compactness property).
- `Γ^{+,1}_U(P)`: the project's `Bd.allowableSections N U` (checked: sc⁺-sections `s` with
  `cl{s ≠ 0} ⊆ U` and `N(s(x)) ≤ 1` for all `x`); `S_g = {x | g(x) = 0_x}`; `f + s` the fibrewise
  sum `sectionAdd`.
- "`(f + s, x)` in good position at every `x ∈ S_{f+s}`": `Bd.IsGoodPositionGermTame (f + s) x`
  (Definition 3.53 in a tame chart, the project's, checked with `#print`, as in V5_29).
- "`S_{f+s}` is a manifold with boundary with corners": a sub-M-polyfold (Definition 2.20) whose
  induced structure (`subPolyfold`, paracompactness asserted) has a compatible manifold-with-corners
  structure (`HasCornerStructure`, Definition 4.1).  Compactness is not part of the quoted claim
  (it follows from the hypothesis on `U`).
- Nothing looks false to me (apart from the reading of "bump functions", see above).
-/
namespace RoundTrip.V5_45
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

end

/-- Theorem 5.25: over a tame M-polyfold with bump functions, for a proper sc-Fredholm section, an
auxiliary norm `N` and an open `U ⊇ S` with `S_{f+s}` compact for `s ∈ Γ^{+,1}_U(P)`, some
`s ∈ Γ^{+,1}_U(P)` puts `(f + s, x)` in good position at every zero `x`, and `S_{f+s}` is a
manifold with boundary with corners. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (N : Bd.One → ℝ) (U : Set X),
    IsTameStrongBundle Bd → PX.AdmitsBumpFunctionsWeak →
    Bd.IsScFredholmSectionTame f → Bd.IsProper f → Bd.IsAuxNorm N →
    IsOpen U → solSet P f ⊆ U →
    (∀ s ∈ Bd.allowableSections N U, IsCompact (solSet P (sectionAdd P f s))) →
      ∃ s ∈ Bd.allowableSections N U,
        (∀ x ∈ solSet P (sectionAdd P f s), Bd.IsGoodPositionGermTame (sectionAdd P f s) x) ∧
        ∃ (hS : PX.IsSubMPolyfold (solSet P (sectionAdd P f s)))
          (_ : ParacompactSpace (solSet P (sectionAdd P f s))),
          (PX.subPolyfold hS).HasCornerStructure

end RoundTrip.V5_45
