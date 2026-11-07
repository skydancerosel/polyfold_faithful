import Polyfold
/-! Blind formalization of V7_9 (the text's Part II, §7.1, Definition 7.7, p. 228 of the 2017
book).

Text: `𝓔𝓟` is the category whose objects are the ep-groupoids and whose morphisms
`f : (X, 𝐗) → (Y, 𝐘)` are the functors which are sc-smooth maps between the object spaces as well
as between the morphism spaces.

Choices:
- This item is a definition.  Setting: ep-groupoids `X : EpGroupoid Obj Mor`,
  `Y : EpGroupoid Obj' Mor'`, `Z : EpGroupoid Obj'' Mor''`, all spaces in `Type` (universe 0),
  Hausdorff paracompact (`RoundTrip/Blind/V7_3.lean`).
- "Functor" between groupoids (`IsFunctorB f₀ f₁`): maps `f₀` on objects and `f₁` on morphisms
  with `s(f₁ φ) = f₀(s φ)`, `t(f₁ φ) = f₀(t φ)`, `f₁(φ ∘ ψ) = f₁ φ ∘ f₁ ψ` for composable pairs,
  `f₁(1_x) = 1_{f₀ x}` (the standard notion; preservation of inverses follows).  A morphism of
  `𝓔𝓟` (`IsEPMorB`): a functor with `f₀`, `f₁` sc-smooth (the project's
  `MPolyfold.IsScSmoothMap`, Definition 2.14).
- B (a)/(b): the project's `EpFunctor X Y` (fields read with `#print`: a `GroupoidFunctor`, whose
  fields are exactly my `IsFunctorB` conditions, plus sc-smoothness on objects and morphisms) is
  exactly such a pair `(f₀, f₁)`.  (c) "`𝓔𝓟` is a category" presupposes that identities are
  morphisms and that composites of morphisms are morphisms: asserted for my `IsEPMorB`.  (d) The
  project's identity and composition (`EpFunctor.id`, `EpFunctor.comp`) are the identity functor
  and the composite functor, and satisfy the category laws (unit laws, associativity).
- The objects of `𝓔𝓟` are the ep-groupoids; the project bundles them as `EP` (a structure with
  the spaces, their instances and an `EpGroupoid`); nothing beyond this bundling is claimed.
- Nothing looks false to me.
-/
namespace RoundTrip.V7_9
open Polyfold

/-- `(f₀, f₁)` is a functor between the groupoids `G` and `H`. -/
def IsFunctorB {Obj Mor Obj' Mor' : Type} (G : GroupoidStr Obj Mor) (H : GroupoidStr Obj' Mor')
    (f₀ : Obj → Obj') (f₁ : Mor → Mor') : Prop :=
  (∀ φ : Mor, H.src (f₁ φ) = f₀ (G.src φ)) ∧
  (∀ φ : Mor, H.tgt (f₁ φ) = f₀ (G.tgt φ)) ∧
  (∀ φ ψ : Mor, G.src φ = G.tgt ψ → f₁ (G.comp φ ψ) = H.comp (f₁ φ) (f₁ ψ)) ∧
  (∀ x : Obj, f₁ (G.unit x) = H.unit (f₀ x))

/-- **Definition 7.7**: `(f₀, f₁)` is a morphism `X → Y` of `𝓔𝓟`: a functor which is sc-smooth
on objects and on morphisms. -/
def IsEPMorB {Obj Mor Obj' Mor' : Type} [TopologicalSpace Obj] [T2Space Obj]
    [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj'] [TopologicalSpace Mor']
    [T2Space Mor'] [ParacompactSpace Mor'] (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor')
    (f₀ : Obj → Obj') (f₁ : Mor → Mor') : Prop :=
  IsFunctorB X.toGroupoidStr Y.toGroupoidStr f₀ f₁ ∧
  X.PObj.IsScSmoothMap Y.PObj f₀ ∧ X.PMor.IsScSmoothMap Y.PMor f₁

/-- Definition 7.7: the project's `EpFunctor`s are the text's morphisms of `𝓔𝓟`; identities and
composites are morphisms; the project's identity and composition are those of functors and obey
the category laws. -/
def B : Prop :=
  ∀ (Obj Mor Obj' Mor' Obj'' Mor'' Obj''' Mor''' : Type)
    [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
    [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor'']
    [TopologicalSpace Obj'''] [T2Space Obj'''] [ParacompactSpace Obj''']
    [TopologicalSpace Mor'''] [T2Space Mor'''] [ParacompactSpace Mor''']
    (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor') (Z : EpGroupoid Obj'' Mor'')
    (W : EpGroupoid Obj''' Mor'''),
    -- (a) every project `EpFunctor` is a morphism of `𝓔𝓟`
    (∀ F : EpFunctor X Y, IsEPMorB X Y F.obj F.mor) ∧
    -- (b) every morphism of `𝓔𝓟` is a project `EpFunctor`
    (∀ (f₀ : Obj → Obj') (f₁ : Mor → Mor'), IsEPMorB X Y f₀ f₁ →
      ∃ F : EpFunctor X Y, F.obj = f₀ ∧ F.mor = f₁) ∧
    -- (c) identities and composites are morphisms of `𝓔𝓟`
    IsEPMorB X X id id ∧
    (∀ (f₀ : Obj → Obj') (f₁ : Mor → Mor') (g₀ : Obj' → Obj'') (g₁ : Mor' → Mor''),
      IsEPMorB X Y f₀ f₁ → IsEPMorB Y Z g₀ g₁ → IsEPMorB X Z (g₀ ∘ f₀) (g₁ ∘ f₁)) ∧
    -- (d) the project's identity and composition, and the category laws
    ((EpFunctor.id X).obj = id ∧ (EpFunctor.id X).mor = id) ∧
    (∀ (F : EpFunctor X Y) (G : EpFunctor Y Z),
      (EpFunctor.comp G F).obj = G.obj ∘ F.obj ∧ (EpFunctor.comp G F).mor = G.mor ∘ F.mor) ∧
    (∀ F : EpFunctor X Y,
      EpFunctor.comp (EpFunctor.id Y) F = F ∧ EpFunctor.comp F (EpFunctor.id X) = F) ∧
    (∀ (F : EpFunctor X Y) (G : EpFunctor Y Z) (H : EpFunctor Z W),
      EpFunctor.comp (EpFunctor.comp H G) F = EpFunctor.comp H (EpFunctor.comp G F))

end RoundTrip.V7_9
