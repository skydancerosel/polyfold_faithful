import Polyfold
/-! Blind formalization of V10_7 (the text's Part II, §10.1, Theorem 10.1.7, p. 465 of the
Springer 2021 book; 2017: Theorem 10.1, p. 337).

Text: if `F` is an equivalence, so is `TF : TX → TY` (full and faithful left to the reader).

Choices:
- Setting: ep-groupoids `X : EpGroupoid Obj Mor`, `Y : EpGroupoid Obj' Mor'`, all four spaces in
  `Type` (universe 0), Hausdorff and paracompact (`RoundTrip/Blind/V7_3.lean`); `F : X → Y` an
  sc-smooth functor (the project's `EpFunctor`, `RoundTrip/Blind/V7_9.lean`).
- `TX`: the project's tangent ep-groupoid `X.tangentEpGroupoid` (Chapter 8's Theorem 8.1.x,
  whose structure maps (8.3)-(8.9) the Chapter 8 blind statements describe, e.g.
  `RoundTrip/Blind/V8_13.lean`); it lives in `Type 1` (Part I's `TangentSpace`), hence my
  notions are universe polymorphic.  `TF`: the project's `F.tangent`.  To pin them down B states:
  `TF = (TΦ, T𝚽)` is Part I's tangent map of `F` on objects and on morphisms
  (`MPolyfold.tangentMap`), the object and morphism M-polyfolds of `TX` are the tangent bundles
  `TX`, `T𝐗` (`MPolyfold.tangentPolyfold`), and its source and target maps are `Ts`, `Tt`
  (stated with an existential proof of the sc-smoothness of `s`, `t`, irrelevant by proof
  irrelevance).  The composition and units of `TX` are not restated.
- "equivalence": my `IsEquivB` (Definition 10.1.1), copied from `RoundTrip/Blind/V10_1.lean`
  (full and faithful; `|F|` a homeomorphism of my quotient-topology orbit spaces; local
  sc-diffeomorphism on objects), here in universe 1 for `TF`.  The parenthetical "full and
  faithful left to the reader" is part of the claim (`IsEquivB` includes it).
- Nothing looks false to me.
-/
namespace RoundTrip.V10_7
open Polyfold

universe u v

section
variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']

/-- `x ≅ y` in the groupoid `G`: there is a morphism `x → y`. -/
def IsoRelB {O M : Type u} (G : GroupoidStr O M) (x y : O) : Prop :=
  ∃ φ : M, G.src φ = x ∧ G.tgt φ = y

/-- The orbit space `|G|`, the objects modulo `≅`, with the quotient topology. -/
abbrev OrbB {O M : Type u} (G : GroupoidStr O M) : Type u :=
  Quot (IsoRelB G)

/-- `F` is full and faithful: `φ ↦ F φ` is a bijection `mor(x, x') → mor(F x, F x')`. -/
def FullyFaithfulB {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (F : EpFunctor X Y) :
    Prop :=
  (∀ φ φ' : Mor, X.src φ = X.src φ' → X.tgt φ = X.tgt φ' → F.mor φ = F.mor φ' → φ = φ') ∧
  (∀ (x x' : Obj) (ψ : Mor'), Y.src ψ = F.obj x → Y.tgt ψ = F.obj x' →
    ∃ φ : Mor, X.src φ = x ∧ X.tgt φ = x' ∧ F.mor φ = ψ)

/-- The induced map `|F| : |X| → |Y|`, `|x| ↦ |F x|`, is a homeomorphism. -/
def OrbitHomeoB {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (F : EpFunctor X Y) :
    Prop :=
  ∃ e : OrbB X.toGroupoidStr ≃ₜ OrbB Y.toGroupoidStr,
    ∀ x : Obj, e (Quot.mk _ x) = Quot.mk _ (F.obj x)

/-- `F` is a local sc-diffeomorphism on objects. -/
def LocalScDiffeoObjB {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (F : EpFunctor X Y) :
    Prop :=
  ∀ x : Obj, ∃ (U : Set Obj) (V : Set Obj') (g : Obj' → Obj),
    x ∈ U ∧ X.PObj.IsScDiffeoOn Y.PObj F.obj g U V

/-- **Definition 10.1.1**: `F` is an equivalence. -/
def IsEquivB {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (F : EpFunctor X Y) : Prop :=
  FullyFaithfulB F ∧ OrbitHomeoB F ∧ LocalScDiffeoObjB F

end

/-- Theorem 10.1.7: the tangent `TF : TX → TY` of an equivalence is an equivalence. -/
def B : Prop :=
  ∀ (Obj Mor Obj' Mor' : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor') (F : EpFunctor X Y),
    -- `TX` and `TF` are the tangent ep-groupoid and the tangent functor
    X.tangentEpGroupoid.PObj = X.PObj.tangentPolyfold ∧
    X.tangentEpGroupoid.PMor = X.PMor.tangentPolyfold ∧
    (∃ (hs : X.PMor.IsScSmoothMap X.PObj X.src) (ht : X.PMor.IsScSmoothMap X.PObj X.tgt),
      X.tangentEpGroupoid.src = MPolyfold.tangentMap hs ∧
      X.tangentEpGroupoid.tgt = MPolyfold.tangentMap ht) ∧
    F.tangent.obj = MPolyfold.tangentMap F.isScSmoothMap_obj ∧
    F.tangent.mor = MPolyfold.tangentMap F.isScSmoothMap_mor ∧
    -- the theorem
    (IsEquivB F → IsEquivB F.tangent)

end RoundTrip.V10_7
