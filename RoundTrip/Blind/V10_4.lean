import Polyfold
/-! Blind formalization of V10_4 (the text's Part II, §10.1, Definition 10.1.4, p. 463 of the
Springer 2021 book; 2017: Definition 10.2, p. 335).

Text: a natural transformation `τ : F → G` of sc-smooth functors is an sc-smooth `τ : X → 𝐘`
with `τ(x) : F(x) → G(x)` and `τ(x') ∘ F(φ) = G(φ) ∘ τ(x)`; `F ≃ G` is an equivalence relation
compatible with composition.

Choices:
- Setting: ep-groupoids `X : EpGroupoid Obj Mor`, `Y : EpGroupoid Obj' Mor'`,
  `Z : EpGroupoid Obj'' Mor''`, all spaces in `Type` (universe 0), Hausdorff and paracompact
  (`RoundTrip/Blind/V7_3.lean`); "sc-smooth functor" is the project's `EpFunctor`
  (`RoundTrip/Blind/V7_9.lean`).
- Natural transformation (`IsNatTransB`, as in `RoundTrip/Blind/V8_15.lean`, the same notion in
  Chapter 8): `τ : Obj → Mor'` sc-smooth from the object M-polyfold of `X` to the morphism
  M-polyfold of `Y` (`MPolyfold.IsScSmoothMap`); `s(τ x) = F x`, `t(τ x) = G x`; for every `φ`
  with `s φ = x`, `t φ = x'`: `τ(x') ∘ F(φ) = G(φ) ∘ τ(x)` (the project's `comp a b = a ∘ b`,
  first `b`).
- `F ≃ G` (`NatEqB`): there is a natural transformation `F → G` (the definition's meaning of
  "naturally equivalent"; in a groupoid every natural transformation is invertible).
- "equivalence relation": `Equivalence NatEqB` on the sc-smooth functors `X → Y`.
- "compatible with composition": `F ≃ F' : X → Y` and `G ≃ G' : Y → Z` give `G ∘ F ≃ G' ∘ F'`;
  the composites are stated as any sc-smooth functors `H`, `H'` with `H = G ∘ F`,
  `H' = G' ∘ F'` on objects and morphisms (an `EpFunctor` is determined by these two maps), so
  the project's `EpFunctor.comp` is not used.
- B also says the project's `EpNatTrans F G` is exactly such a `τ` (its `app`) and the project's
  `EpFunctor.NaturallyEquivalent` is `NatEqB`.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_4
open Polyfold

section
variable {Obj Mor Obj' Mor' : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']

/-- **Definition 10.1.4**: `τ` is a natural transformation `F → G`: sc-smooth `X → 𝐘`,
`τ(x) : F(x) → G(x)`, and `τ(x') ∘ F(φ) = G(φ) ∘ τ(x)` for `φ : x → x'`. -/
def IsNatTransB {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (F G : EpFunctor X Y)
    (τ : Obj → Mor') : Prop :=
  X.PObj.IsScSmoothMap Y.PMor τ ∧
  (∀ x : Obj, Y.src (τ x) = F.obj x ∧ Y.tgt (τ x) = G.obj x) ∧
  (∀ (φ : Mor) (x x' : Obj), X.src φ = x → X.tgt φ = x' →
    Y.comp (τ x') (F.mor φ) = Y.comp (G.mor φ) (τ x))

/-- `F ≃ G`: there is a natural transformation `F → G`. -/
def NatEqB {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (F G : EpFunctor X Y) : Prop :=
  ∃ τ : Obj → Mor', IsNatTransB F G τ

end

/-- Definition 10.1.4: natural transformations and `F ≃ G` (the project's notions are these);
`≃` is an equivalence relation, compatible with composition. -/
def B : Prop :=
  ∀ (Obj Mor Obj' Mor' Obj'' Mor'' : Type)
    [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
    [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor'']
    (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor') (Z : EpGroupoid Obj'' Mor''),
    -- the project's natural transformations and natural equivalence are the text's
    (∀ F G : EpFunctor X Y,
      (∀ τ : EpNatTrans F G, IsNatTransB F G τ.app) ∧
      (∀ τ : Obj → Mor', IsNatTransB F G τ → ∃ T : EpNatTrans F G, T.app = τ) ∧
      (F.NaturallyEquivalent G ↔ NatEqB F G)) ∧
    -- `≃` is an equivalence relation
    Equivalence (fun F G : EpFunctor X Y => NatEqB F G) ∧
    -- `≃` is compatible with composition
    (∀ (F F' : EpFunctor X Y) (G G' : EpFunctor Y Z) (H H' : EpFunctor X Z),
      H.obj = G.obj ∘ F.obj → H.mor = G.mor ∘ F.mor →
      H'.obj = G'.obj ∘ F'.obj → H'.mor = G'.mor ∘ F'.mor →
      NatEqB F F' → NatEqB G G' → NatEqB H H')

end RoundTrip.V10_4
