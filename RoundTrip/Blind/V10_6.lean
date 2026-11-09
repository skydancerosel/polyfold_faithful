import Polyfold
/-! Blind formalization of V10_6 (the text's Part II, §10.1, Proposition 10.1.6, p. 464 of the
Springer 2021 book; 2017: Proposition 10.3, p. 336).

Text: if `F : X → Y` and `Φ ∘ F` are equivalences and `Φ` is sc-smooth, then `Φ` is an
equivalence.

Choices:
- Setting: ep-groupoids `X : EpGroupoid Obj Mor`, `Y : EpGroupoid Obj' Mor'`,
  `Z : EpGroupoid Obj'' Mor''`, all spaces in `Type` (universe 0), Hausdorff and paracompact
  (`RoundTrip/Blind/V7_3.lean`).  "`Φ` is sc-smooth": `Φ : Y → Z` is an sc-smooth functor (the
  project's `EpFunctor`, `RoundTrip/Blind/V7_9.lean`); `F` is one too (an equivalence is an
  sc-smooth functor by definition).
- "equivalence": my `IsEquivB` (Definition 10.1.1), copied from `RoundTrip/Blind/V10_1.lean`
  (full and faithful; `|F|` a homeomorphism of my quotient-topology orbit spaces; local
  sc-diffeomorphism on objects).
- `Φ ∘ F`: any sc-smooth functor `H : X → Z` with `H = Φ ∘ F` on objects and on morphisms (an
  `EpFunctor` is determined by these maps; the project's `EpFunctor.comp` is not used).
- Nothing looks false to me.
-/
namespace RoundTrip.V10_6
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

/-- Proposition 10.1.6: if `F` and `Φ ∘ F` are equivalences and `Φ` is an sc-smooth functor, then
`Φ` is an equivalence. -/
def B : Prop :=
  ∀ (Obj Mor Obj' Mor' Obj'' Mor'' : Type)
    [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
    [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor'']
    (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor') (Z : EpGroupoid Obj'' Mor'')
    (F : EpFunctor X Y) (Φ : EpFunctor Y Z) (H : EpFunctor X Z),
    H.obj = Φ.obj ∘ F.obj → H.mor = Φ.mor ∘ F.mor →
    IsEquivB F → IsEquivB H → IsEquivB Φ

end RoundTrip.V10_6
