import Polyfold
/-! Blind formalization of V10_32 (the text's Part II, §10.3, the properties (E1)–(E3) of the
class `E`, p. 483 of the Springer 2021 book; 2017 p. 347).

Text: (E1) the isomorphisms of `𝓔𝓟` are equivalences; (E2) composites of equivalences are
equivalences; (E3) a functor naturally equivalent to an equivalence is an equivalence.

Choices:
- Setting: ep-groupoids `X : EpGroupoid Obj Mor`, `Y : EpGroupoid Obj' Mor'`,
  `Z : EpGroupoid Obj'' Mor''`, all spaces in `Type` (universe 0), Hausdorff and paracompact as
  the project's `EpGroupoid` requires (as in `RoundTrip/Blind/V7_9.lean`, `V10_1.lean`); the
  morphisms of `𝓔𝓟` are the project's `EpFunctor`s (checked in V7_9).
- "equivalence" (Definition 10.1.1) is the project's `EpFunctor.IsEquivalence` (fields read with
  `#print`: full, faithful, `|F|` a homeomorphism, local sc-diffeomorphism on objects); I trust it
  (it is characterized in `RoundTrip/Blind/V10_1.lean`).
- (E1) "isomorphism of `𝓔𝓟`" (`IsIsoB`, my own): an sc-smooth functor `F : X → Y` with an
  sc-smooth functor `G : Y → X` inverse to it on objects and on morphisms (`G ∘ F = 1`,
  `F ∘ G = 1`, written componentwise, so the project's identity functor is not used).
- (E2) the composite `G ∘ F` is the project's `EpFunctor.comp` (`G.comp F`; checked to be the
  composite functor in V7_9).  The text's "when the composition is defined" is built into the
  types.
- (E3) "naturally equivalent" (`≃`, Definition 10.1.4): there is a natural transformation, the
  project's `EpNatTrans` (fields read with `#print`: sc-smooth `τ : X → 𝐘`, `τ(x) : F(x) → G(x)`,
  naturality; characterized in `RoundTrip/Blind/V10_4.lean`).  The direction of `≃` is not fixed:
  B assumes a natural transformation `F → G` or one `G → F` (the relation is symmetric anyway).
- Nothing looks false to me.
-/
namespace RoundTrip.V10_32
open Polyfold

section
variable {Obj Mor Obj' Mor' : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']

/-- `F` is an isomorphism of `𝓔𝓟`: an sc-smooth functor `G` in the other direction is inverse to
`F` on objects and on morphisms. -/
def IsIsoB {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (F : EpFunctor X Y) : Prop :=
  ∃ G : EpFunctor Y X,
    (∀ x : Obj, G.obj (F.obj x) = x) ∧ (∀ φ : Mor, G.mor (F.mor φ) = φ) ∧
    (∀ y : Obj', F.obj (G.obj y) = y) ∧ (∀ ψ : Mor', F.mor (G.mor ψ) = ψ)

end

/-- (E1)–(E3): isomorphisms are equivalences, composites of equivalences are equivalences, and a
functor naturally equivalent to an equivalence is an equivalence. -/
def B : Prop :=
  ∀ (Obj Mor Obj' Mor' Obj'' Mor'' : Type)
    [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
    [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor'']
    (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor') (Z : EpGroupoid Obj'' Mor''),
    -- (E1) every isomorphism of `𝓔𝓟` is an equivalence
    (∀ F : EpFunctor X Y, IsIsoB F → F.IsEquivalence) ∧
    -- (E2) the composite of two equivalences is an equivalence
    (∀ (F : EpFunctor X Y) (G : EpFunctor Y Z), F.IsEquivalence → G.IsEquivalence →
      (G.comp F).IsEquivalence) ∧
    -- (E3) a functor naturally equivalent to an equivalence is an equivalence
    (∀ F G : EpFunctor X Y, F.IsEquivalence →
      (Nonempty (EpNatTrans F G) ∨ Nonempty (EpNatTrans G F)) → G.IsEquivalence)

end RoundTrip.V10_32
