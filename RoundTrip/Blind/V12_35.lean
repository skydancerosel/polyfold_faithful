import Polyfold
/-! Blind formalization of V12_35 (the text's Part II, §12.3, Theorem 12.3.9, pp. 586–587 of the
Springer 2021 book; 2017: Theorem 12.8).

Text: `(P : W → X, μ)` a strong bundle over a tame ep-groupoid with `|X|` paracompact, admitting
sc-smooth partitions of unity; `s` an sc⁺-section functor of `W|∂X`, `U` a saturated open
neighbourhood of `∂X`.  Then there is an sc⁺-section functor `s̃` supported in `U` with
`s̃|∂X = s`.  Moreover, given an auxiliary norm `N` and `δ > 0` with `N(s(x)) < δ` on `∂X`, `s̃`
can be chosen with `N(s̃(x)) ≤ δ` for all `x`.

Choices:
- Setting as in `RoundTrip/Blind/V12_4.lean` (universe 0, `E : EpStrongBundle X B`,
  paracompactness of `𝐗 ₛ×_P W` as an instance hypothesis).  "tame": `X.IsTame`; "`|X|`
  paracompact": `X.HasParacompactOrbitSpace`; "admitting sc-smooth partitions of unity":
  `X.HasScPartitionsOfUnity` (Definition 7.5.5, read with `#print`: for every saturated open
  cover a subordinate sc-smooth partition of unity, locally finite on saturated neighbourhoods
  and invariant under morphisms).
- `∂X = X.PObj.boundary`.  "sc⁺-section functor of `W|∂X`": the project's
  `EpStrongBundle.IsBoundaryScPlusSectionFunctor` (read with `#print`: Part I's Definition 5.4.1,
  `StrongBundle.IsBoundaryScPlusSection` — on `∂X` a section with values in `W_{0,1}`, sc⁺ on
  every local face in every tame chart — plus `s(t φ) = μ(φ, s(s φ))` for morphisms `φ` with
  `s(φ) ∈ ∂X`).  `s : Obj → W` is a total function; only its values on `∂X` matter.
- "sc⁺-section functor" (of `W`): `E.IsScPlusSectionFunctor` (Definition 8.3.4 (2), read with
  `#print`: an sc-smooth section functor which is an sc⁺-section).  "supported in `U`":
  `supp s̃ = cl{x | s̃(x) ≠ 0_x} ⊆ U` (`sectionSupport`, read with `#print`; the closure in the
  object space).  "`s̃|∂X = s`": `s̃(x) = s(x)` for `x ∈ ∂X`.  "saturated open neighbourhood of
  `∂X`": `U` open, `X.IsSaturated U` (`π⁻¹(π(U)) = U`), `∂X ⊆ U`.
- "auxiliary norm": `EpStrongBundle.IsAuxNorm` (as in V12_4), a function on `W_{0,1}`.
  "`N(s(x)) < δ`" for `x ∈ ∂X`: `s(x) ∈ W_{0,1}` and `N(s(x)) < δ` (`NormLt`, my own);
  "`N(s̃(x)) ≤ δ` for all `x`": `B.AuxLe N (s̃ x) δ` (read with `#print`: `s̃(x) ∈ W_{0,1}` and
  `N(s̃(x)) ≤ δ`; sc⁺-sections take values in `W_{0,1}`).
- The "moreover" part: under its extra hypotheses there is an `s̃` with all properties of the
  first part and the bound.  B is the conjunction of both parts.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V12_35
open Polyfold

section
variable {Obj : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  {PX : MPolyfold Obj} {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W]
  {P : W → Obj} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- `w ∈ W_{0,1}` and `N(w) < δ`. -/
def NormLt (B : StrongBundle PX P) (N : B.One → ℝ) (w : W) (δ : ℝ) : Prop :=
  ∃ hw : w ∈ B.oneSet, N (B.oneMk w hw) < δ

end

/-- **Theorem 12.3.9**: an sc⁺-section functor of `W|∂X` extends to an sc⁺-section functor of `W`
supported in a given saturated open neighbourhood of `∂X`, with an auxiliary norm bound
`≤ δ` if the boundary section has norm `< δ`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (W : Type) [TopologicalSpace W] [T2Space W] [ParacompactSpace W] (P : W → Obj)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle X.PObj P)
    [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X B),
    X.IsTame → X.HasParacompactOrbitSpace → X.HasScPartitionsOfUnity →
    ∀ s : Obj → W, E.IsBoundaryScPlusSectionFunctor s →
    ∀ U : Set Obj, IsOpen U → X.IsSaturated U → X.PObj.boundary ⊆ U →
      -- an extension supported in `U`
      (∃ s' : Obj → W, E.IsScPlusSectionFunctor s' ∧ sectionSupport P s' ⊆ U ∧
        ∀ x ∈ X.PObj.boundary, s' x = s x) ∧
      -- with the norm bound
      (∀ (N : B.One → ℝ) (δ : ℝ), E.IsAuxNorm N → 0 < δ →
        (∀ x ∈ X.PObj.boundary, NormLt B N (s x) δ) →
        ∃ s' : Obj → W, E.IsScPlusSectionFunctor s' ∧ sectionSupport P s' ⊆ U ∧
          (∀ x ∈ X.PObj.boundary, s' x = s x) ∧ ∀ x : Obj, B.AuxLe N (s' x) δ)

end RoundTrip.V12_35
