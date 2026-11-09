import Polyfold
/-! Blind formalization of V11_40 (the text's Part II, §11.6, the category `𝒫𝒞` and
Definition 11.6.7, p. 561 of the Springer 2021 book; 2017: Definition 11.8, p. 410).

Text: proper coverings and their functors form a category `𝒫𝒞` with the class `E_𝒫𝒞`; a diagram
is `F ←Γ A →ε F'` with `Γ ∈ E_𝒫𝒞`, and two diagrams have a common refinement if there are
equivalences `H`, `H'` with `Γ ∘ H ≃ Γ' ∘ H'`, `ε ∘ H ≃ ε' ∘ H'`.

Choices:
- This item is a definition (with the implicit claim that `𝒫𝒞` is a category).  Setting: the
  project's bundled proper coverings `PC.{0}` (`#print`ed: ep-groupoids `Y`, `X` as objects of
  the project's `EP` (Definition 7.7), an `EpFunctor F : Y → X` and a proof of
  `EpFunctor.IsProperCovering`), all spaces in `Type`, with the project's category instance;
  diagrams the project's `PC.Diagram`; middle objects `A`, `A''` in `PC.{0}` as well.
- B says: (a) the objects of `PC` are the proper coverings (every `c : PC` is one, every proper
  covering occurs); its morphisms `A ⟶ B` are the project's `ProperCoveringHom A.F B.F` (the
  functors of Definition 11.6.4 (1), characterized in my `RoundTrip/Blind/V11_36.lean`), the
  identity is `(1_Y, 1_X)` and the composition is componentwise (stated on the object and
  morphism maps); (b) the project's `PC.equivalences` is the class of equivalences of
  Definition 11.6.4 (2), my `IsEquivB` (copied from V11_36: `Ψ`, `Φ` equivalences of ep-groupoids
  in the project's sense `EpFunctor.IsEquivalence`, checked in `RoundTrip/Blind/V10_1.lean`, and
  `Ψ` bijective from `Y_x` onto `Y'_{Φ(x)}`); (c) a diagram `d : F.Diagram F'` is exactly a
  triple `(A, Γ, ε)` with `Γ : A → F` in `E_𝒫𝒞` and `ε : A → F'` (the map `d ↦ (A, Γ, ε)` into
  the sigma type is injective with image the triples with `IsEquivB Γ`); (d) the project's
  `HasCommonRefinement` is my `HasCommonRefinementB`.
- Composition of functors of proper coverings is componentwise, `Γ ∘ H = (Ψ_Γ ∘ Ψ_H, Φ_Γ ∘ Φ_H)`
  (with the project's `EpFunctor.comp`).  "`≃`" (my `NatEquivB`, Definition 11.6.5, my
  `RoundTrip/Blind/V11_37.lean`): there is a natural transformation of functors between proper
  coverings, i.e. a pair of `EpNatTrans` `τ_Y`, `τ_X` with `τ_X ∘ F_{A''} = F_{target} ∘ τ_Y`
  (11.20), from the first functor to the second (direction irrelevant: targets are groupoids).
  "equivalences `H : A'' → A`, `H' : A'' → A'`": `IsEquivB`.  The project's `NaturallyEquivalent`,
  `ProperCoveringHom.comp`, `IsEquivalence` are not used in (d).
- Nothing looks false to me.
-/
namespace RoundTrip.V11_40
open Polyfold CategoryTheory

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

/-- The data `(A, Γ, ε)` of a diagram `F ←Γ A →ε F'`. -/
def diagDataB {F F' : PC.{0}} (d : F.Diagram F') :
    Σ A : PC.{0}, ProperCoveringHom A.F F.F × ProperCoveringHom A.F F'.F :=
  ⟨d.A, d.Γ, d.ε⟩

/-- Definition 11.6.7: `d = (F ←Γ A →ε F')` and `d' = (F ←Γ' A' →ε' F')` have a common
refinement: equivalences `H : A'' → A`, `H' : A'' → A'` with `Γ ∘ H ≃ Γ' ∘ H'` and
`ε ∘ H ≃ ε' ∘ H'`. -/
def HasCommonRefinementB {F F' : PC.{0}} (d d' : F.Diagram F') : Prop :=
  ∃ (A'' : PC.{0}) (H : ProperCoveringHom A''.F d.A.F) (H' : ProperCoveringHom A''.F d'.A.F),
    IsEquivB H ∧ IsEquivB H' ∧
    NatEquivB A''.F F.F (d.Γ.Ψ.comp H.Ψ) (d'.Γ.Ψ.comp H'.Ψ) (d.Γ.Φ.comp H.Φ) (d'.Γ.Φ.comp H'.Φ) ∧
    NatEquivB A''.F F'.F (d.ε.Ψ.comp H.Ψ) (d'.ε.Ψ.comp H'.Ψ) (d.ε.Φ.comp H.Φ) (d'.ε.Φ.comp H'.Φ)

/-- The category `𝒫𝒞` of proper coverings, its class `E_𝒫𝒞`, its diagrams and their common
refinements (Definition 11.6.7) are the text's. -/
def B : Prop :=
  -- (a) objects: the proper coverings
  (∀ c : PC.{0}, c.F.IsProperCovering) ∧
  (∀ (Y X : EP.{0}) (F : EpFunctor Y.X X.X), F.IsProperCovering →
    ∃ c : PC.{0}, c.Y = Y ∧ c.X = X ∧ HEq c.F F) ∧
  -- morphisms: the functors `(Ψ, Φ)` of proper coverings
  (∀ A B : PC.{0}, (A ⟶ B) = ProperCoveringHom A.F B.F) ∧
  -- identity `(1_Y, 1_X)`
  (∀ A : PC.{0}, (𝟙 A : A ⟶ A).Ψ.obj = id ∧ (𝟙 A : A ⟶ A).Ψ.mor = id ∧
    (𝟙 A : A ⟶ A).Φ.obj = id ∧ (𝟙 A : A ⟶ A).Φ.mor = id) ∧
  -- composition `(Ψ₂ ∘ Ψ₁, Φ₂ ∘ Φ₁)`
  (∀ (A B C : PC.{0}) (f : A ⟶ B) (g : B ⟶ C),
    (f ≫ g).Ψ.obj = g.Ψ.obj ∘ f.Ψ.obj ∧ (f ≫ g).Ψ.mor = g.Ψ.mor ∘ f.Ψ.mor ∧
    (f ≫ g).Φ.obj = g.Φ.obj ∘ f.Φ.obj ∧ (f ≫ g).Φ.mor = g.Φ.mor ∘ f.Φ.mor) ∧
  -- (b) the class `E_𝒫𝒞` of equivalences
  (∀ (A B : PC.{0}) (f : A ⟶ B),
    PC.equivalences f ↔ IsEquivB (show ProperCoveringHom A.F B.F from f)) ∧
  -- (c) diagrams `F ←Γ A →ε F'` with `Γ ∈ E_𝒫𝒞`
  (∀ F F' : PC.{0}, Function.Injective (diagDataB (F := F) (F' := F')) ∧
    Set.range (diagDataB (F := F) (F' := F')) = {p | IsEquivB p.2.1}) ∧
  -- (d) common refinements
  (∀ (F F' : PC.{0}) (d d' : F.Diagram F'), d.HasCommonRefinement d' ↔ HasCommonRefinementB d d')

end RoundTrip.V11_40
