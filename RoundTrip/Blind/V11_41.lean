import Polyfold
/-! Blind formalization of V11_41 (the text's Part II, §11.6, Proposition 11.6.8, p. 562 of the
Springer 2021 book; 2017: Proposition 11.8, p. 411).

Text: if `d, d'` and `d', d''` have common refinements, so have `d, d''`.

Choices:
- Setting as in my `RoundTrip/Blind/V11_40.lean`: `F`, `F'` objects of the project's bundled
  category of proper coverings `PC.{0}` (all spaces in `Type`), diagrams `d, d', d'' : F → F'`
  the project's `PC.Diagram F F'` (characterized in V11_40 as the triples `F ←Γ A →ε F'` with
  `Γ ∈ E_𝒫𝒞`).  The refining object `A''` ranges over `PC.{0}`.
- "have a common refinement": my `HasCommonRefinementB` of V11_40 (Definition 11.6.7), copied
  here with `IsEquivB` (Definition 11.6.4 (2)) and `NatEquivB` (Definition 11.6.5, (11.20)); the
  project's `HasCommonRefinement`, `CommonRefinement`, `NaturallyEquivalent`,
  `ProperCoveringHom.comp`, `IsEquivalence` are not used.
- Nothing looks false to me.
-/
namespace RoundTrip.V11_41
open Polyfold

section
variable {ObjY MorY : Type} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjX MorX : Type} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {ObjY' MorY' : Type} [TopologicalSpace ObjY'] [T2Space ObjY'] [ParacompactSpace ObjY']
  [TopologicalSpace MorY'] [T2Space MorY'] [ParacompactSpace MorY']
  {ObjX' MorX' : Type} [TopologicalSpace ObjX'] [T2Space ObjX'] [ParacompactSpace ObjX']
  [TopologicalSpace MorX'] [T2Space MorX'] [ParacompactSpace MorX']
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX}
  {Y' : EpGroupoid ObjY' MorY'} {X' : EpGroupoid ObjX' MorX'}

/-- Definition 11.6.4 (2): `(Ψ, Φ) : F → F'` is an equivalence. -/
def IsEquivB {F : EpFunctor Y X} {F' : EpFunctor Y' X'} (Γ : ProperCoveringHom F F') : Prop :=
  Γ.Ψ.IsEquivalence ∧ Γ.Φ.IsEquivalence ∧
    ∀ x : ObjX, Set.BijOn Γ.Ψ.obj (F.obj ⁻¹' {x}) (F'.obj ⁻¹' {Γ.Φ.obj x})

/-- Definition 11.6.5: the functors `(ζ, ξ), (ζ', ξ') : G → F'` are naturally equivalent: there
are natural transformations `τ_Y : ζ → ζ'`, `τ_X : ξ → ξ'` with `τ_X ∘ G = F' ∘ τ_Y` (11.20). -/
def NatEquivB (G : EpFunctor Y X) (F' : EpFunctor Y' X') (ζ ζ' : EpFunctor Y Y')
    (ξ ξ' : EpFunctor X X') : Prop :=
  ∃ (τY : EpNatTrans ζ ζ') (τX : EpNatTrans ξ ξ'), ∀ y : ObjY, τX.app (G.obj y) = F'.mor (τY.app y)

end

/-- Definition 11.6.7: `d = (F ←Γ A →ε F')` and `d' = (F ←Γ' A' →ε' F')` have a common
refinement: equivalences `H : A'' → A`, `H' : A'' → A'` with `Γ ∘ H ≃ Γ' ∘ H'` and
`ε ∘ H ≃ ε' ∘ H'`. -/
def HasCommonRefinementB {F F' : PC.{0}} (d d' : F.Diagram F') : Prop :=
  ∃ (A'' : PC.{0}) (H : ProperCoveringHom A''.F d.A.F) (H' : ProperCoveringHom A''.F d'.A.F),
    IsEquivB H ∧ IsEquivB H' ∧
    NatEquivB A''.F F.F (d.Γ.Ψ.comp H.Ψ) (d'.Γ.Ψ.comp H'.Ψ) (d.Γ.Φ.comp H.Φ) (d'.Γ.Φ.comp H'.Φ) ∧
    NatEquivB A''.F F'.F (d.ε.Ψ.comp H.Ψ) (d'.ε.Ψ.comp H'.Ψ) (d.ε.Φ.comp H.Φ) (d'.ε.Φ.comp H'.Φ)

/-- Proposition 11.6.8: having a common refinement is transitive. -/
def B : Prop :=
  ∀ (F F' : PC.{0}) (d d' d'' : F.Diagram F'),
    HasCommonRefinementB d d' → HasCommonRefinementB d' d'' → HasCommonRefinementB d d''

end RoundTrip.V11_41
